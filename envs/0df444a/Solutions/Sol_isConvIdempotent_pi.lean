-- Prove2me | solution 1 for isConvIdempotent_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:52.218137+00:00
-- url     : https://prove2.me/submissions/9e477e65-adcd-4cea-b53d-b2a00b12c337

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhProdConv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PhProdConv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PhProdConv.ProdConv := by
  intro ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv
  refine ⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩
  unfold PI.PhProdConv.PhConv
  refine ⟨?_, fun g => ?_, fun x y => ?_⟩
  · exact Finset.prod_eq_one (fun i _ => (hconv i).1)
  · change ∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))
  · have key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) =
        fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i) := by
      funext g
      rw [← Finset.prod_mul_distrib]
      rfl
    change MeasureTheory.Integrable
        (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i))
        (MeasureTheory.Measure.pi μ) ∧
      ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g
        ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)
    rw [key]
    refine ⟨MeasureTheory.Integrable.fintype_prod_dep
      (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)
