-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_selfadj_of_central_idem
-- name    : Formalism.L2.SG.Pf.AllRowsGA.selfadj_of_central_idem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:20.490109+00:00
-- url     : https://prove2.me/theorems/b1bb37d5-5b0b-5030-8847-75c2233d109d
-- title:
--   All Rows GA: selfadj of central idem
-- statement:
--   The All Rows GA construction uses the selfadj of central idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L80-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.SG.Pf.AllRowsGA.selfadj_of_central_idem (e : MonoidAlgebra ℂ G) (hid : e * e = e) (hc : ∀ y, e * y = y * e) :
    conjA e = e := by sorry
