-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_contDiff_clm_comp
-- name    : Formalism.FourierDecayAlt.P.NFRadRedS.contDiff_clm_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:18:11.717857+00:00
-- url     : https://prove2.me/theorems/05e51cdc-b3b1-5ed7-858f-0ccbe6e81a89
-- title:
--   NFRad Red S: cont Diff clm comp
-- statement:
--   The NFRad Red S construction uses the cont Diff clm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L33-L37

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical

theorem Formalism.FourierDecayAlt.P.NFRadRedS.contDiff_clm_comp {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] :
    ContDiff ℝ ∞ (fun p : (F →L[ℂ] G) × (E →L[ℂ] F) => p.1.comp p.2) := by sorry
