-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_regularity_at_place
-- name    : Formalism.FourierDecayAlt.P.regularity_at_place
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:18.070196+00:00
-- url     : https://prove2.me/theorems/9fec63ee-7d86-46f1-bba6-7269998c58a2
-- title:
--   P: regularity at place
-- statement:
--   The P construction uses the regularity at place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L379-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L379-L390

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.regularity_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (hb : 0 ≤ b)
    (hexp : ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
      ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
      (∀ i, TBB.jN2 p (fi i) ≤ TBB.jN2 p f) ∧
      (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fi i) (P.r + 1) [] (TBB.bigPt P.r c))) ∧
      ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
        ((D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (TBB.bigPt P.r c) =
          ∑ i, co i • p.V (fi i) (TBB.bigPt P.r c)) :
    Formalism.FourierDecayAlt.TBB.RegularityBoundBigCell p f b C₃ a₁ := by sorry
