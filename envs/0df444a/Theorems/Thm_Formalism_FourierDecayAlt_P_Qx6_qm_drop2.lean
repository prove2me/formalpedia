-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_drop2
-- name    : Formalism.FourierDecayAlt.P.Qx6.qm_drop2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:33.557036+00:00
-- url     : https://prove2.me/theorems/5deda96c-dec7-4f97-9c7a-a81971cc477a
-- title:
--   Qx6: qm drop2
-- statement:
--   The Qx6 construction uses the qm drop2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L431-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L431-L442

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

theorem Formalism.FourierDecayAlt.P.Qx6.qm_drop2 (hFR : ExpFirstRow) (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (g : Fin t → Fin n)
    (b : Fin (t + 1) → Fin n) (e s : Fin n) (w : Fin t) (u : ℂ) :
    qminor E (bE e (bS g s) ∘ w.castSucc.succ.succAbove) b u =
      ∑ x' : Fin (t + 1), ∑ x : Fin t, ((-1 : ℤ) ^ ((x' : ℕ) + (t + 1 + (x : ℕ)))) •
        (Tm E (u - 1 - (t : ℂ) + 1) s (b (x'.succAbove x)) *
          qminor E (g ∘ skip1 w) ((b ∘ x'.succAbove) ∘ skip1 x) (u - 1) * Tm E u e (b x')) := by sorry
