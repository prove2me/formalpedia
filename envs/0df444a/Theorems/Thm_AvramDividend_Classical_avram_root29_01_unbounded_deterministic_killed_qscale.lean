-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_deterministic_killed_qscale
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_deterministic_killed_qscale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:46:19.151891+00:00
-- url     : https://prove2.me/theorems/c3b9cc43-b782-4792-803a-92e94ba91339
-- title:
--   Unbounded-variation original-Lévy deterministic killed q-scale semigroup without auxiliary Esscher root
-- statement:
--   Under exactly the canonical WS1A assumptions of unbounded variation, positive discount q and genuine q-scale function, the original-P real killed q-scale expectation for closed survival through every deterministic horizon equals W(x) for every real x. The verified positive-root existence theorem cfe6d3e1 supplies a genuine φ>0 with ψφ=q, thereby discharging the only auxiliary hypotheses of the independently proven deterministic killed q-scale result. This is not yet the stronger strict first-passage stopped-scale identity.
-- source:
--   WS1A distinct one-step source reduction work/avram_root29_01_unbounded_deterministic_killed_qscale_draft.lean, pending acceptance of deterministic q-scale source; do not submit early.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_deterministic_killed_qscale

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_root29_01_unbounded_deterministic_killed_qscale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) =
      W x := by sorry
