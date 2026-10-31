-- Prove2me | Theorems.Thm_ForkJoinDelay_eq_1_2_key_recursion
-- name    : ForkJoinDelay.eq_1_2_key_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:16.337787+00:00
-- url     : https://prove2.me/theorems/fddeaed2-a229-4e01-9ca0-caec62b1b5cf
-- title:
--   Eqs. (1)–(2) — the key recursion for $\Psi_{k,h_1,h_2}$
-- statement:
--   Consider the fork-join network with exponential services of rates $\mu_0,\mu_1,\mu_2>0$, and complex $w_0,w_{FJ}$ with $\operatorname{Re}w_0\ge0$, $\operatorname{Re}w_{FJ}\ge0$. For every $k\ge1$ and $h_1,h_2\ge0$, conditioning on the remaining service time $t$ of the customer in service at $Q_0$ and on the numbers of completions at UFJ and LFJ during $[0,t]$,
--
--   $$\Psi_{k,h_1,h_2}(w_0,w_{FJ})=\int_0^\infty e^{-w_0t}\,X_{k,h_1,h_2}(t)\,\mu_0e^{-\mu_0t}\,dt,$$
--
--   where, with $p_i(r)=e^{-\mu_it}(\mu_it)^r/r!$,
--
--   $$\begin{aligned}X_{k,h_1,h_2}(t)={}&\sum_{r_1=0}^{h_1-1}\sum_{r_2=0}^{h_2-1}p_1(r_1)p_2(r_2)\,\Psi_{k-1,h_1-r_1+1,h_2-r_2+1}+\sum_{r_1=0}^{h_1-1}\sum_{r_2=h_2}^{\infty}p_1(r_1)p_2(r_2)\,\Psi_{k-1,h_1-r_1+1,1}\\&+\sum_{r_1=h_1}^{\infty}\sum_{r_2=0}^{h_2-1}p_1(r_1)p_2(r_2)\,\Psi_{k-1,1,h_2-r_2+1}+\sum_{r_1=h_1}^{\infty}\sum_{r_2=h_2}^{\infty}p_1(r_1)p_2(r_2)\,\Psi_{k-1,1,1},\end{aligned}$$
--
--   all transforms evaluated at $(w_0,w_{FJ})$, and empty sums equal to $0$.
--
--   The four terms are the four cases for the fork-join stations during that service: some or all customers served at each station. This is the step that reduces the state $k$ to $k-1$.
--
--   **Formalization Note** The transforms on both sides are those of the same explicit model.
--
--   Differences from the source:
--   - encoding: E_{k,h1,h2}[·]: expectation given the state (k, h1, h2) at the tagged customer's arrival → expectation in an explicit FCFS construction from i.i.d. exponential services (residual services included), no arrivals after the tagged customer (IsFJModel, sojournQ0, sojournFJ); reason: the paper's own argument: residual services are exponential by memorylessness (pp.9–10) and later arrivals do not matter (p.8)
--   - reading: FJ stations may be single-, multiple- or infinite-server; 'From here on, we shall assume both stations in the FJ part have a single server' (p.8) → single-server FCFS stations UFJ and LFJ; reason: the paper fixes single servers on p.8 and (2) is the single-server formula
--   - reading: service 'rates' µ0, µ1, µ2 → 0 < µ0, µ1, µ2; reason: a rate of an exponential law is positive
--   - generalization: transform arguments w0, wFJ (domain not stated; LST on real w ≥ 0) → complex w0, wFJ with Re w0 ≥ 0, Re wFJ ≥ 0; reason: real w ≥ 0 is the special case; the paper evaluates the transform at imaginary arguments (Fourier inversion, p.13); every formula is defined there
--   - reading: (1)–(3) derived 'for the case where k,h1,h2 > 0'; p.11: (3) 'remains valid when an empty sum is defined to be zero' for h1 = 0 or h2 = 0 → every h1, h2 ≥ 0, with empty finite sums (Finset.range) for h = 0; reason: the paper's own extension on p.11 (and p.9: 'the cases h1 = 0 and h2 = 0 follow from the same analysis')
--   - encoding: Ψ_{k,·,·} expressed through Ψ_{k−1,·,·}, k ≥ 1 → stated at k + 1 in terms of k, for every k ≥ 0; reason: natural-number indexing; same instances
--   - encoding: infinite sums Σ_{r=h}^∞ → tsum over n with r = h + n; reason: the families are absolutely summable, so the tsum is the true sum
--   - encoding: ∫_0^∞ … dt → Bochner integral over Set.Ioi 0; reason: the integrands are integrable on (0, ∞); same value
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eqs. (1)–(2), pp.9–10

import Mathlib
import Definitions.Def_ForkJoinDelay_IsFJModel
import Definitions.Def_ForkJoinDelay_psi

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The key recursion, Eqs. (1)–(2).**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eqs. (1)–(2), pp.9–10. Conditioning on the remaining service time
`t` of the customer in service at `Q₀` (density `µ₀e^{−µ₀t}`), and on the numbers of service
completions at UFJ and LFJ during `[0, t]` (Poisson while the station stays busy):

`Ψ_{k,h₁,h₂} = ∫₀^∞ e^{−w₀t} X_{k,h₁,h₂}(t) µ₀e^{−µ₀t} dt`, with
`X = Σ_{r₁<h₁} Σ_{r₂<h₂} p₁(r₁) p₂(r₂) Ψ_{k−1,h₁−r₁+1,h₂−r₂+1}
   + Σ_{r₁<h₁} Σ_{r₂≥h₂} p₁(r₁) p₂(r₂) Ψ_{k−1,h₁−r₁+1,1}
   + Σ_{r₁≥h₁} Σ_{r₂<h₂} p₁(r₁) p₂(r₂) Ψ_{k−1,1,h₂−r₂+1}
   + Σ_{r₁≥h₁} Σ_{r₂≥h₂} p₁(r₁) p₂(r₂) Ψ_{k−1,1,1}`,
`pᵢ(r) = e^{−µᵢt}(µᵢt)^r / r!`.

Stated here with `k + 1` in place of `k` (so `k ≥ 1` in the paper's indexing), for **every**
`h₁, h₂ ≥ 0` (empty finite sums for `h = 0`), every positive rates, and every complex
`w₀, w_FJ` with nonnegative real parts. The transforms `Ψ_{k,·,·}` on the right are those of the
same model.

**Formalization Note.** The infinite sums over `r ≥ h` are written as `tsum`s over `n` with
`r = h + n`. The integral over `(0, ∞)` is the Bochner integral on `Set.Ioi 0`. -/
theorem eq_1_2_key_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₀ μ₁ μ₂ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (V U G : ℕ → Ω → ℝ) (hM : IsFJModel P μ₀ μ₁ μ₂ V U G)
    (w₀ wFJ : ℂ) (hw₀ : 0 ≤ w₀.re) (hwFJ : 0 ≤ wFJ.re) (k h₁ h₂ : ℕ) :
    psi P V U G (k + 1) h₁ h₂ w₀ wFJ =
      ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(w₀ * t)) *
        ((∑ r₁ ∈ Finset.range h₁, ∑ r₂ ∈ Finset.range h₂,
            ((Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ r₁ / (r₁.factorial : ℝ) *
              (Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ r₂ / (r₂.factorial : ℝ)) : ℝ) : ℂ) *
              psi P V U G k (h₁ - r₁ + 1) (h₂ - r₂ + 1) w₀ wFJ) +
          (∑ r₁ ∈ Finset.range h₁, ∑' n : ℕ,
            ((Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ r₁ / (r₁.factorial : ℝ) *
              (Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ (h₂ + n) / ((h₂ + n).factorial : ℝ)) : ℝ) : ℂ) *
              psi P V U G k (h₁ - r₁ + 1) 1 w₀ wFJ) +
          (∑' n : ℕ, ∑ r₂ ∈ Finset.range h₂,
            ((Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ (h₁ + n) / ((h₁ + n).factorial : ℝ) *
              (Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ r₂ / (r₂.factorial : ℝ)) : ℝ) : ℂ) *
              psi P V U G k 1 (h₂ - r₂ + 1) w₀ wFJ) +
          (∑' n : ℕ, ∑' m : ℕ,
            ((Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ (h₁ + n) / ((h₁ + n).factorial : ℝ) *
              (Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ (h₂ + m) / ((h₂ + m).factorial : ℝ)) : ℝ) : ℂ) *
              psi P V U G k 1 1 w₀ wFJ)) *
        ((μ₀ * Real.exp (-(μ₀ * t)) : ℝ) : ℂ) := by sorry

end ForkJoinDelay
