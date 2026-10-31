-- Prove2me | Theorems.Thm_ForkJoinDelay_eq_3_recursion
-- name    : ForkJoinDelay.eq_3_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:07.694266+00:00
-- url     : https://prove2.me/theorems/586f15db-b0d9-4ee9-9f76-2098d75a4614
-- title:
--   Eq. (3) — the recursion for $\Psi_{k,h_1,h_2}$, $k\ge1$
-- statement:
--   In the fork-join network with rates $\mu_0,\mu_1,\mu_2>0$ and for complex $w_0,w_{FJ}$ with nonnegative real parts, for every $k\ge1$ and $h_1,h_2\ge0$,
--
--   $$\begin{aligned}\Psi_{k,h_1,h_2}={}&\sum_{r_1=0}^{h_1-1}\sum_{r_2=0}^{h_2-1}\Psi_{k-1,h_1-r_1+1,h_2-r_2+1}\,a(r_1,r_2)+\sum_{r_1=0}^{h_1-1}\Psi_{k-1,h_1-r_1+1,1}\,b(r_1,h_2)\\&+\sum_{r_2=0}^{h_2-1}\Psi_{k-1,1,h_2-r_2+1}\,c(h_1,r_2)+\Psi_{k-1,1,1}\,d(h_1,h_2),\end{aligned}$$
--
--   with all transforms at $(w_0,w_{FJ})$, the coefficients $a,b,c,d$ of (4), and empty sums ($h_1=0$ or $h_2=0$) equal to $0$.
--
--   The recursion expresses the transform in state $k$ through finitely many transforms in state $k-1$; iterating it reduces every state to $k=0$.
--
--   **Formalization Note** Both sides concern the transform of the explicit model; the right-hand side is the definition `recStep` applied to the table of $\Psi_{k-1,\cdot,\cdot}$.
--
--   Differences from the source:
--   - encoding: E_{k,h1,h2}[·]: expectation given the state (k, h1, h2) at the tagged customer's arrival → expectation in an explicit FCFS construction from i.i.d. exponential services (residual services included), no arrivals after the tagged customer (IsFJModel, sojournQ0, sojournFJ); reason: the paper's own argument: residual services are exponential by memorylessness (pp.9–10) and later arrivals do not matter (p.8)
--   - reading: FJ stations may be single-, multiple- or infinite-server; 'From here on, we shall assume both stations in the FJ part have a single server' (p.8) → single-server FCFS stations UFJ and LFJ; reason: the paper fixes single servers on p.8 and (2) is the single-server formula
--   - reading: service 'rates' µ0, µ1, µ2 → 0 < µ0, µ1, µ2; reason: a rate of an exponential law is positive
--   - generalization: transform arguments w0, wFJ (domain not stated; LST on real w ≥ 0) → complex w0, wFJ with Re w0 ≥ 0, Re wFJ ≥ 0; reason: real w ≥ 0 is the special case; the paper evaluates the transform at imaginary arguments (Fourier inversion, p.13); every formula is defined there
--   - reading: (1)–(3) derived 'for the case where k,h1,h2 > 0'; p.11: (3) 'remains valid when an empty sum is defined to be zero' for h1 = 0 or h2 = 0 → every h1, h2 ≥ 0, with empty finite sums (Finset.range) for h = 0; reason: the paper's own extension on p.11 (and p.9: 'the cases h1 = 0 and h2 = 0 follow from the same analysis')
--   - encoding: Ψ_{k,·,·} expressed through Ψ_{k−1,·,·}, k ≥ 1 → stated at k + 1 in terms of k, for every k ≥ 0; reason: natural-number indexing; same instances
--   - encoding: a(r1,r2) defined as an integral (p.10) → a(r1,r2) in the closed form of (4) (coefA); b, c, d the tsums of it; reason: the closed form is proved in (4); milestone eq_4_coefficients states that the two agree
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eq. (3), p.11, with the note after it

import Mathlib
import Definitions.Def_ForkJoinDelay_IsFJModel
import Definitions.Def_ForkJoinDelay_psi
import Definitions.Def_ForkJoinDelay_recStep

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The recursion (3) for `k ≥ 1`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eq. (3), p.11:

`Ψ_{k,h₁,h₂} = Σ_{r₁=0}^{h₁−1} Σ_{r₂=0}^{h₂−1} Ψ_{k−1,h₁−r₁+1,h₂−r₂+1} a(r₁,r₂)
  + Σ_{r₁=0}^{h₁−1} Ψ_{k−1,h₁−r₁+1,1} b(r₁,h₂) + Σ_{r₂=0}^{h₂−1} Ψ_{k−1,1,h₂−r₂+1} c(h₁,r₂)
  + Ψ_{k−1,1,1} d(h₁,h₂)`,

"if h1 = 0 and/or h2 = 0, (3) remains valid when an empty sum is defined to be zero".

Stated with `k + 1` in place of `k`, for every `h₁, h₂ ≥ 0`, positive rates and complex
`w₀, w_FJ` with nonnegative real parts. Both sides are about the model's transform `psi`;
`recStep` is the right-hand side of (3) with `a` in closed form and `b, c, d` its tail sums. -/
theorem eq_3_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₀ μ₁ μ₂ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (V U G : ℕ → Ω → ℝ) (hM : IsFJModel P μ₀ μ₁ μ₂ V U G)
    (w₀ wFJ : ℂ) (hw₀ : 0 ≤ w₀.re) (hwFJ : 0 ≤ wFJ.re) (k h₁ h₂ : ℕ) :
    psi P V U G (k + 1) h₁ h₂ w₀ wFJ =
      recStep μ₀ μ₁ μ₂ w₀ (fun x y => psi P V U G k x y w₀ wFJ) h₁ h₂ := by sorry

end ForkJoinDelay
