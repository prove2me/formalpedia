-- Prove2me | Theorems.Thm_EthierKurtz_sde_exists_bounded_lipschitz
-- name    : EthierKurtz.sde_exists_bounded_lipschitz
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:50:56.987458+00:00
-- url     : https://prove2.me/theorems/d030bb59-8c04-431d-998a-c401364c4b13
-- title:
--   Strong existence for Brownian SDEs with bounded, globally Lipschitz coefficients
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion and let $s:\mathbb R^d\to\mathbb R^{d\times d}$, $b:\mathbb R^d\to\mathbb R^d$ be continuous, bounded entrywise by $S$, and globally Lipschitz with constant $L$. Then for every $x_0$ the equation
--
--   $$X_t=x_0+\int_0^t s(X_u)\,dW_u+\int_0^t b(X_u)\,du$$
--
--   has a strong solution on the given Brownian motion (a continuous adapted process satisfying it a.s. for all $t$).
--
--   Role: the Picard-iteration existence theorem applied to the truncated Kolmogorov coefficients in the proof of existence in Lemma 3.1.
-- source:
--   I. Karatzas, S. E. Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113, 1991, https://doi.org/10.1007/978-1-4612-0949-2, Theorem 5.2.9 (strong existence under Lipschitz and linear growth conditions), p. 289

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem sde_exists_bounded_lipschitz {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    (x₀ : SDEState d) {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d}
    (hs : Continuous s) (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S)
    (hbS : ∀ x i, |b x i| ≤ S) {L : ℝ}
    (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖) :
    ∃ X : ℝ≥0 → Ω → SDEState d,
      SolvesBrownianSDE P (fun p => s p.2) (fun p => b p.2) W (fun _ => x₀) X := by sorry

end EthierKurtz
