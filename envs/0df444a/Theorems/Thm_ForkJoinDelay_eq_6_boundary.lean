-- Prove2me | Theorems.Thm_ForkJoinDelay_eq_6_boundary
-- name    : ForkJoinDelay.eq_6_boundary
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:09.012993+00:00
-- url     : https://prove2.me/theorems/5e2336f3-a317-4309-8222-d82590ccb656
-- title:
--   Eq. (6) — the boundary recursion for $\Psi_{0,h_1,h_2}$
-- statement:
--   In the fork-join network with rates $\mu_0,\mu_1,\mu_2>0$ and for complex $w_0,w_{FJ}$ with nonnegative real parts, when the tagged customer finds nobody at $Q_0$ ($k=0$), for every $h_1,h_2\ge0$,
--
--   $$\begin{aligned}\Psi_{0,h_1,h_2}={}&\sum_{r_1=0}^{h_1-1}\sum_{r_2=0}^{h_2-1}Z_{h_1-r_1+1,h_2-r_2+1}\,a(r_1,r_2)+\sum_{r_1=0}^{h_1-1}Z_{h_1-r_1+1,1}\,b(r_1,h_2)\\&+\sum_{r_2=0}^{h_2-1}Z_{1,h_2-r_2+1}\,c(h_1,r_2)+Z_{1,1}\,d(h_1,h_2),\end{aligned}$$
--
--   where $Z_{x,y}=Z_{x,y}(w_{FJ})$ is the boundary transform (5), $a,b,c,d$ are the coefficients of (4), and empty sums equal $0$.
--
--   This is the base of the recursion in $k$: once $k=0$, the transform is a finite combination of the explicit transforms $Z_{x,y}$.
--
--   Differences from the source:
--   - encoding: E_{k,h1,h2}[·]: expectation given the state (k, h1, h2) at the tagged customer's arrival → expectation in an explicit FCFS construction from i.i.d. exponential services (residual services included), no arrivals after the tagged customer (IsFJModel, sojournQ0, sojournFJ); reason: the paper's own argument: residual services are exponential by memorylessness (pp.9–10) and later arrivals do not matter (p.8)
--   - reading: FJ stations may be single-, multiple- or infinite-server; 'From here on, we shall assume both stations in the FJ part have a single server' (p.8) → single-server FCFS stations UFJ and LFJ; reason: the paper fixes single servers on p.8 and (2) is the single-server formula
--   - reading: service 'rates' µ0, µ1, µ2 → 0 < µ0, µ1, µ2; reason: a rate of an exponential law is positive
--   - generalization: transform arguments w0, wFJ (domain not stated; LST on real w ≥ 0) → complex w0, wFJ with Re w0 ≥ 0, Re wFJ ≥ 0; reason: real w ≥ 0 is the special case; the paper evaluates the transform at imaginary arguments (Fourier inversion, p.13); every formula is defined there
--   - reading: (1)–(3) derived 'for the case where k,h1,h2 > 0'; p.11: (3) 'remains valid when an empty sum is defined to be zero' for h1 = 0 or h2 = 0 → every h1, h2 ≥ 0, with empty finite sums (Finset.range) for h = 0; reason: the paper's own extension on p.11 (and p.9: 'the cases h1 = 0 and h2 = 0 follow from the same analysis')
--   - encoding: a(r1,r2) defined as an integral (p.10) → a(r1,r2) in the closed form of (4) (coefA); b, c, d the tsums of it; reason: the closed form is proved in (4); milestone eq_4_coefficients states that the two agree
--   - encoding: Z_{x,y}(wFJ) := E[e^{−wFJ SFJ} | h1 = x, h2 = y] = ∫_0^∞ e^{−wFJ t} dF_{SFJ|x,y}(t) (5) → ∫ e^{−wFJ max(s,t)} d(Gamma(x,µ1) ⊗ Gamma(y,µ2)) (boundaryLST); reason: p.12 identifies (S1|h1 = x) ∼ Gamma(x,µ1), (S2|h2 = y) ∼ Gamma(y,µ2), independent; milestone sec_3_1_fj_cdf connects the two
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eq. (6), p.12, with Eq. (5), p.12, and the note on p.13

import Mathlib
import Definitions.Def_ForkJoinDelay_IsFJModel
import Definitions.Def_ForkJoinDelay_psi
import Definitions.Def_ForkJoinDelay_boundaryLST
import Definitions.Def_ForkJoinDelay_recStep

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The boundary recursion (6) for `k = 0`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eq. (6), p.12, with (5), p.12, and p.13:

`Ψ_{0,h₁,h₂} = Σ_{r₁=0}^{h₁−1} Σ_{r₂=0}^{h₂−1} Z_{h₁−r₁+1,h₂−r₂+1} a(r₁,r₂)
  + Σ_{r₁=0}^{h₁−1} Z_{h₁−r₁+1,1} b(r₁,h₂) + Σ_{r₂=0}^{h₂−1} Z_{1,h₂−r₂+1} c(h₁,r₂)
  + Z_{1,1} d(h₁,h₂)`,

"an empty sum (h1 = 0 and/or h2 = 0) is again defined to be zero". Here the tagged customer
finds nobody at `Q₀`, and `Z_{x,y}` (`boundaryLST`) is the transform of the maximum of
independent `Gamma(x, µ₁)` and `Gamma(y, µ₂)` sojourn times, `x, y` counting the tagged
customer.

Stated for every `h₁, h₂ ≥ 0`, positive rates and complex `w₀, w_FJ` with nonnegative real
parts; the left side is the model's transform `psi` with `k = 0`. -/
theorem eq_6_boundary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₀ μ₁ μ₂ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (V U G : ℕ → Ω → ℝ) (hM : IsFJModel P μ₀ μ₁ μ₂ V U G)
    (w₀ wFJ : ℂ) (hw₀ : 0 ≤ w₀.re) (hwFJ : 0 ≤ wFJ.re) (h₁ h₂ : ℕ) :
    psi P V U G 0 h₁ h₂ w₀ wFJ =
      recStep μ₀ μ₁ μ₂ w₀ (fun x y => boundaryLST μ₁ μ₂ x y wFJ) h₁ h₂ := by sorry

end ForkJoinDelay
