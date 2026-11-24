-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_dropS
-- name    : Formalism.FourierDecayAlt.P.Qx6.qm_dropS
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:02.00787+00:00
-- url     : https://prove2.me/theorems/c3c38e41-618b-4a5c-bd6a-d34c2ea1b884
-- title:
--   Qx6: qm drop S
-- statement:
--   The Qx6 construction uses the qm drop S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L331-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L331-L342

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
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

theorem Formalism.FourierDecayAlt.P.Qx6.qm_dropS (hFR : ExpFirstRow) (hSk : QSkewRow) (hE : GlRel E) : ∀ {m : ℕ} (v b : Fin m → Fin n) (s : Fin n)
    (w : Fin m) (u : ℂ),
    qminor E (bS v s ∘ w.castSucc.succAbove) b u = ∑ x : Fin m, ((-1 : ℤ) ^ (m + 1 + (x : ℕ))) •
      (Tm E (u - (m : ℂ) + 1) s (b x) * qminor E (v ∘ skip1 w) (b ∘ skip1 x) u)
  := by sorry
