-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_of_not_dv
-- name    : Formalism.HermitianLattices.Ext.L3.U0.unit_of_not_dv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:44.233794+00:00
-- url     : https://prove2.me/theorems/64fd8ac0-3075-4773-a829-f87f727813e2
-- title:
--   U0: unit of not dv
-- statement:
--   The U0 construction uses the unit of not dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L105-L107

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}

theorem Formalism.HermitianLattices.Ext.L3.U0.unit_of_not_dv (hπ : IsUnif S π) {s : K} (hs : s ∈ S) (hf : star s = s)
    (hn : ¬ Dv S π s) : IsUnitIn S s := by sorry
