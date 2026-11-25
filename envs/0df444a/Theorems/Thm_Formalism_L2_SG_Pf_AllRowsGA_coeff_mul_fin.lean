-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin
-- name    : Formalism.L2.SG.Pf.AllRowsGA.coeff_mul_fin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:15.001732+00:00
-- url     : https://prove2.me/theorems/2f19378f-134f-4e76-ba10-3bd530d10a7d
-- title:
--   All Rows GA: coeff mul fin
-- statement:
--   The All Rows GA construction uses the coeff mul fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L11-L13

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

theorem Formalism.L2.SG.Pf.AllRowsGA.coeff_mul_fin (a b : MonoidAlgebra ℂ G) (g : G) :
    (a * b).coeff g = ∑ h : G, a.coeff h * b.coeff (h⁻¹ * g) := by sorry
