-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_grid_exit_integrable_finite_cap
-- name    : AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_integrable_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:13:07.033346+00:00
-- url     : https://prove2.me/theorems/4be55ddb-4f53-42f2-9b3a-c607994248dd
-- title:
--   Discounted HJB terminal value is integrable at a bounded finite-grid exit
-- statement:
--   Under a finite nonnegative real dividend reserve cap c, a capped-admissible strategy, root HJB regularity/gradient and nonnegativity hypotheses, and the already Proved finite-grid hittingBtwn stopping-index interface, the discounted post-payment HJB candidate at the random grid exit clock K is integrable. Previously Proved stopped-grid measurability handles ω↦exp(-q clock K)w(Uplus_{clock K}); the proven HJB all-times nonnegativity gives w(Uplus)≥0; a separate previously Proved finite-cap theorem gives deterministic B≥0 such that w(Uplus_t)≤B at all t and outcomes. As q>0 and clock K≥0, 0<exp(-q clock K)≤1, so the random terminal payoff is pointwise in [0,B]. Since P is a probability measure, measurable bounded real functions are integrable. This provides a new stopping-time integrability interface but does not prove Itô calculus, generator drift inequality or expected dividend upper bound.
-- source:
--   Proved targets 4162f708-75f3-4924-9994-2b002bffe95e, f7029cc5-793e-418f-9446-2904e497f1b5 and 3e30828d-bef6-424c-afe5-36b4c72e7a60; Integrable.of_mem_Icc.

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_grid_exit_stopped_measurable
import Theorems.Thm_AvramDividend_Classical_capped_postPayment_candidate_uniform_upper_bound_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_postPayment_terminal_nonnegative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_integrable_finite_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max
        (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω -
          rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    Integrable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        w (x + X.X (clock (K ω)) ω -
          rightLimit D (clock (K ω)) ω)) P := by sorry
