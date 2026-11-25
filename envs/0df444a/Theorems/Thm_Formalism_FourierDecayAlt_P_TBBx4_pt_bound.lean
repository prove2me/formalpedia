-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_pt_bound
-- name    : Formalism.FourierDecayAlt.P.TBBx4.pt_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:01:36.89205+00:00
-- url     : https://prove2.me/theorems/060b50a0-2823-43ed-aecd-ff8c626c21cc
-- title:
--   TBBx4: pt bound
-- statement:
--   The TBBx4 construction uses the pt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L245-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L245-L281

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

theorem Formalism.FourierDecayAlt.P.TBBx4.pt_bound (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {n : ℕ}
    (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ) (a : ℕ) (γ : C.LPt)
    (hexp : D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      ((D.ptMatN γ (P.r + 1)).det ^ a) • p.V f γ = ∑ i, co i • p.V (fi i) γ) :
    ‖(D.ptMatN γ (P.r + 1)).det‖ ^ (2 * a) * Ew p (fun _ => 1) f (P.r + 1) [] γ ≤
      (∑ i, ‖co i‖) * ∑ i, ‖co i‖ * Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ := by sorry
