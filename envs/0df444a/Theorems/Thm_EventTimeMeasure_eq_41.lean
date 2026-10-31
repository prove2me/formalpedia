-- Prove2me | Theorems.Thm_EventTimeMeasure_eq_41
-- name    : EventTimeMeasure.eq_41
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:55.309095+00:00
-- url     : https://prove2.me/theorems/ea37ef5e-5533-420b-bdf3-954cd2c91b01
-- title:
--   (41), p.28 — integration by parts: $Z_t=1+\int_0^t Z_{s-}(u_s-1)\,dM_s$ for the single-event density
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying the event timing model of §2.1: standard exponential thresholds $\xi_1,\dots,\xi_n$, clock filtrations $\mathbb H_i$, nonnegative $\mathbb H_i$-progressive hazard rates $h^i$ with clocks $H^i_t=\int_0^t h^i_s\,ds$ (finite for finite $t$, $H^i_\infty=\infty$), event times $\tau_i=\inf\{t>0: H^i_t\ge\xi_i\}$, indicators $N^i_t=\mathbf 1\{\tau_i\le t\}$, intensities $p^i_s=h^i_s\mathbf 1\{\tau_i>s\}$, and a right-continuous information filtration $\mathbb F\supseteq\mathbb H_i$ making every $\tau_i$ a stopping time. The multiplier $u=(u^1,\dots,u^n)$ has $u^i\ge 0$ $\mathbb H_i$-predictable and locally bounded, $Q^i_t=\int_0^t u^i_s h^i_s\,ds$ (7), and $Z_\infty=\exp\bigl(\sum_i (H^i-Q^i)_{\tau_i}\bigr)\prod_i u^i_{\tau_i}$ (fn 17).
--
--   At the induction step of Appendix A the events $1,\dots,\ell$ are already tilted: $\mathbb Q_\ell=Z^\ell_\infty P$, where $Z^\ell_\infty$ is $Z_\infty$ with $u^i=1$ for $i>\ell$. For the next event (index $\ell+1$, whose sub- and superscripts the paper drops) let
--   $$Z_t=\exp\Bigl(\int_0^t(1-u_s)p_s\,ds+N_t\log u_\tau\Bigr)=e^{(H-Q)_{t\wedge\tau}}\,\bigl(u_\tau\ \text{if}\ \tau\le t,\ \text{else } 1\bigr),\qquad 0\le t\le\infty,$$
--   $Z_{s-}$ its left limit, and $\theta_k=\inf\{t\ge 0:\int_0^t(1+u_s)h_s\,ds\ge k\}$ (40), $k\in\mathbb N$.
--
--   With $M=N-\int_0^\cdot p_s\,ds$, the integration-by-parts formula
--   $$Z_t=1+\int_0^t Z_{s-}(u_s-1)\,dM_s \qquad (41)$$
--   holds pathwise: for almost every $\omega$ and every $t\in[0,\infty]$,
--   $$Z_t-1=(u_\tau-1)Z_{\tau-}\mathbf 1\{\tau\le t\}-\int_0^{t\wedge\tau}Z_{s-}(u_s-1)h_s\,ds.$$
--
--   It is the first step of the proof: it exhibits $Z$ as a local martingale whose localization by $\theta_k$ the next steps control.
--
--   **Formalization Note** The stated event is any $j$ (`Fin n`). The $dN$ part of the integral is the single jump at $\tau$ and $\int_0^t(\cdot)p_s\,ds=\int_0^{t\wedge\tau}(\cdot)h_s\,ds$; the $ds$ integral is a Bochner integral whose integrand is integrable almost surely.
--
--   Differences from the source:
--   - generalization: stated inside the proof of Theorem 3.1 under all its hypotheses, including the independence assumptions of §2.1 → assumes only the event timing model and that u is a multiplier; no independence, compensator or hazard condition; reason: a pathwise calculus identity; the source's setting is a special case
--   - generalization: 𝔽 is the progressive enlargement of ℍ_1 ∨ ⋯ ∨ ℍ_n by the τ_i (fn 7, p.5); the probability space and the filtrations are complete; the τ_i are totally inaccessible → 𝔽 is any right-continuous filtration containing every ℍ_i for which every τ_i is a stopping time; completeness, total inaccessibility and almost-sure distinctness of the τ_i are not assumed; n = 0 is allowed; reason: the progressive enlargement is such a filtration, so the statement specializes to the source's; the identity is pathwise and uses neither total inaccessibility nor distinctness; n = 0 is vacuous here
--   - reading: §3, p.9: u^i is nonnegative, ℍ_i-predictable and locally bounded (the filtration of the localization is not named) → IsMultiplier: u^i is ℍ_i-predictable (Mathlib IsStronglyPredictable) and locally bounded along a localizing sequence of 𝔽-stopping times (Mathlib Locally); reason: the weaker hypothesis of the two readings: localization in ℍ_i implies localization in 𝔽, since ℍ_i ⊆ 𝔽
--   - encoding: time [0, ∞); H^i continuous, increasing, H^i_0 = 0, H^i_t = ∫_0^t h^i_s ds (3); τ_i = inf{t > 0 : H^i_t ≥ ξ_i} (2) → time ℝ≥0; H^i_t is the lower Lebesgue integral of h^i over [0, t] in ℝ≥0∞ for t ∈ [0, ∞], finite at finite t almost surely; τ_i takes values in [0, ∞] = WithTop ℝ≥0 with inf ∅ = ∞; reason: Lean convention; continuity, monotonicity and H^i_0 = 0 follow from the integral form (3), and no instance changes
--   - encoding: Z_t = exp(∫_0^t (1 − u_s) p_s ds + N_t log(u_τ)) for the event ℓ + 1, with Z_{s−} its left limit (p.27) → zProc: exp((H − Q)_{t∧τ}) · (u_τ if τ ≤ t, else 1) for t ∈ [0, ∞]; zProcLeft: the same with τ < s; ℚ_ℓ = Z^ℓ_∞ P is simMeasure (uBefore u ℓ); on the P-null event {τ = ∞}, u_τ is read as u_0; reason: ∫_0^t (1 − u_s) p_s ds = (H − Q)_{t∧τ}; the factor form is exp(N_t log u_τ) with log 0 = −∞, and t ↦ (H − Q)_{t∧τ} is continuous, so zProcLeft is the left limit; {τ = ∞} is also ℚ_ℓ-null, since ℚ_ℓ ≪ P
--   - encoding: the stochastic integral ∫_0^t Z_{s−}(u_s − 1) dM_s with dM = dN − p ds → the pathwise expression (u_τ − 1) Z_{τ−} 1{τ ≤ t} − ∫_0^{t∧τ} Z_{s−}(u_s − 1) h_s ds (Bochner integral); reason: N has a single unit jump at τ and p_s = h_s 1{s < τ}; the integrand is integrable almost surely
-- source:
--   Giesecke–Shkolnik, Reducing Bias in Event Time Simulations via Measure Changes, authors' manuscript of January 16, 2018 (Math. Oper. Res., doi:10.1287/moor.2021.1156), Appendix A, eq. (41), p.28

import Mathlib
import Definitions.Def_EventTimeMeasure_Model
import Definitions.Def_EventTimeMeasure_MeasureChange

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace EventTimeMeasure

/-- **Integration by parts for the single-event density, eq. (41)** (Giesecke–Shkolnik,
*Reducing Bias in Event Time Simulations via Measure Changes*, manuscript of January 16, 2018,
Appendix A, eq. (41), p.28): `Z_t = 1 + ∫_0^t Z_{s−}(u_s − 1) dM_s`, `M = N − ∫_0^· p_s ds`.

For event `j` and almost every `ω`, for every `t ∈ [0, ∞]` (the range `0 ≤ t ≤ ∞` of p.27),
`Z_t − 1 = (u_τ − 1) Z_{τ−} 1{τ ≤ t} − ∫_0^{t∧τ} Z_{s−}(u_s − 1) h_s ds`.

**Formalization Note** The stochastic integral against `dM = dN − p ds` is written pathwise: the
`dN` part is the single jump at `τ`, and `∫_0^t … p_s ds = ∫_0^{t∧τ} … h_s ds`. The `ds`
integral is a Bochner integral over `[0, t ∧ τ]`; its integrand is integrable almost surely. -/
theorem eq_41 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (hu : M.IsMultiplier u) (j : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : WithTop ℝ≥0,
      M.zProc u j t ω - 1 =
        (if M.τ j ω ≤ t then
            (((u j ((M.τ j ω).untopD 0) ω : ℝ≥0) : ℝ) - 1) *
              M.zProcLeft u j ((M.τ j ω).untopD 0) ω
          else 0) -
        ∫ s in {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ min t (M.τ j ω)},
          M.zProcLeft u j s ω * (((u j s ω : ℝ≥0) : ℝ) - 1) * ((M.h j s ω : ℝ≥0) : ℝ) ∂leb := by sorry

end EventTimeMeasure
