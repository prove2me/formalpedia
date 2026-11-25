-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_tau_normSq
-- name    : Formalism.L2.SG.Pf.AllRowsTr.tau_normSq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:56.790252+00:00
-- url     : https://prove2.me/theorems/9845604f-1c9b-4c30-905e-2f3b5f422025
-- title:
--   All Rows Tr: tau norm Sq
-- statement:
--   The All Rows Tr construction uses the tau norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L26-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsTr
open Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.SG.Pf.AllRowsTr.tau_normSq (x : MonoidAlgebra ℂ G) :
    (conjA x * x).coeff 1 = ((∑ h : G, Complex.normSq (x.coeff h) : ℝ) : ℂ) := by sorry
