-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_regularity_at_place_of_expansion
-- name    : Formalism.FourierDecayAlt.P.TBBx4.regularity_at_place_of_expansion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:59:40.591295+00:00
-- url     : https://prove2.me/theorems/ee9d3c41-4285-4c5c-8f58-354ef0e30cf5
-- title:
--   TBBx4: regularity at place of expansion
-- statement:
--   The TBBx4 construction uses the regularity at place of expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L283-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L283-L335

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem Formalism.FourierDecayAlt.P.TBBx4.regularity_at_place_of_expansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ)
    (hb : 0 ≤ b)
    (hexp : ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
      ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
      (∀ i, jN2 p (fi i) ≤ jN2 p f) ∧
      (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] (bigPt P.r c))) ∧
      ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (bigPt P.r c) (P.r + 1) → 0 < Gp p (bigPt P.r c) →
        ((D.ptMatN (bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (bigPt P.r c) =
          ∑ i, co i • p.V (fi i) (bigPt P.r c)) :
    RegularityBoundBigCell p f b C₃ a₁ := by sorry
