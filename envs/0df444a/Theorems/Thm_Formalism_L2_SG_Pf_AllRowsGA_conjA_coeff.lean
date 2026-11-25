-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_coeff
-- name    : Formalism.L2.SG.Pf.AllRowsGA.conjA_coeff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:11.024439+00:00
-- url     : https://prove2.me/theorems/c1aede3d-f6f0-528e-92a7-d31bd2a02b70
-- title:
--   All Rows GA: conj A coeff
-- statement:
--   The All Rows GA construction uses the conj A coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L28-L29

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

theorem Formalism.L2.SG.Pf.AllRowsGA.conjA_coeff (a : MonoidAlgebra ℂ G) (g : G) : (conjA a).coeff g = star (a.coeff g⁻¹) := by sorry
