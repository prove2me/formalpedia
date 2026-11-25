-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_central_of_class
-- name    : Formalism.L2.SG.Pf.AllRowsGA.central_of_class
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:30.151727+00:00
-- url     : https://prove2.me/theorems/6e9cdddd-cf9b-4d51-8ea6-9a4e0b59ef72
-- title:
--   All Rows GA: central of class
-- statement:
--   The All Rows GA construction uses the central of class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean#L15-L23

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

theorem Formalism.L2.SG.Pf.AllRowsGA.central_of_class (a : MonoidAlgebra ℂ G) (h : ∀ g P : G, a.coeff (P⁻¹ * g * P) = a.coeff g)
    (y : MonoidAlgebra ℂ G) : a * y = y * a := by sorry
