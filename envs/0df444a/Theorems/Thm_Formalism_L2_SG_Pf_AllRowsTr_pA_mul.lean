-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_pA_mul
-- name    : Formalism.L2.SG.Pf.AllRowsTr.pA_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:27.338203+00:00
-- url     : https://prove2.me/theorems/c5f34e43-fc76-59ba-af74-7c32985ab5b6
-- title:
--   All Rows Tr: p A mul
-- statement:
--   The All Rows Tr construction uses the p A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L52-L60

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

theorem Formalism.L2.SG.Pf.AllRowsTr.pA_mul (f g : ∀ i, MonoidAlgebra ℂ (G i)) : pA f * pA g = pA (fun i => f i * g i) := by sorry
