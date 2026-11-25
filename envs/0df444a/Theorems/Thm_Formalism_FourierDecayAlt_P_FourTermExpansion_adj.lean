-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_adj
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.adj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:14:22.906066+00:00
-- url     : https://prove2.me/theorems/e1d09303-de66-4015-950a-ef350e18fab7
-- title:
--   Four Term Expansion: adj
-- statement:
--   The Four Term Expansion construction uses the adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L364-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L364-L393

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
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
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.adj {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ)
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc ((m + 1 : ℕ) : ℕ∞) Φ g) :
    qminorOp (Q.EH k r) a (b ∘ Equiv.swap i.castSucc i.succ) u Φ g = -qminorOp (Q.EH k r) a b u Φ g := by sorry
