-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_tau_conj
-- name    : Formalism.L2.SG.Pf.AllRowsTr.tau_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:32:03.682427+00:00
-- url     : https://prove2.me/theorems/97e8d9f7-02c9-597c-be2b-35ea9a8bd058
-- title:
--   All Rows Tr: tau conj
-- statement:
--   The All Rows Tr construction uses the tau conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean#L21-L24

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

theorem Formalism.L2.SG.Pf.AllRowsTr.tau_conj (P : G) (a : MonoidAlgebra ℂ G) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1).coeff 1 = a.coeff 1 := by sorry
