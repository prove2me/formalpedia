-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_rowW
-- name    : Formalism.FourierDecayAlt.P.Qx6.qm_rowW
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:35:34.729957+00:00
-- url     : https://prove2.me/theorems/c9fd0477-b730-4197-8209-61d55b1b46ed
-- title:
--   Qx6: qm row W
-- statement:
--   The Qx6 construction uses the qm row W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L444-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L444-L473

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem Formalism.FourierDecayAlt.P.Qx6.qm_rowW (hFC : ExpFirstCol) (hFR : ExpFirstRow) (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E)
    (e es : Fin n) : ∀ {m : ℕ} (v : Fin m → Fin n), IsBorder e es v → ∀ (w : Fin m) (u : ℂ),
    qminor E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bE e v) u =
      Tm E u e e * qminor E (bS v es ∘ w.castSucc.succAbove) v (u - 1) +
      ((-1 : ℤ) ^ m) • (E es e * qminor E (bE e v ∘ w.succ.succAbove) v (u - 1)) +
      ∑ W : Fin m, ∑ X : Fin m, ∑ X' : Fin m, if W ≠ w ∧ X ≠ X' then
        ((-1 : ℤ) ^ (m + 1 + (w : ℕ)) * (sg2 W w * sg2 X X')) •
          (E (v W) e * E es (v X) *
            qminor E (v ∘ skip2 (min W w) (max W w)) (v ∘ skip2 (min X X') (max X X')) (u - 2) * E e (v X'))
        else 0
  := by sorry
