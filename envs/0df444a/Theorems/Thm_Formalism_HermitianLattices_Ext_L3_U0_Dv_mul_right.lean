-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_right
-- name    : Formalism.HermitianLattices.Ext.L3.U0.Dv.mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:32.245962+00:00
-- url     : https://prove2.me/theorems/be39d6c4-3c33-4585-b45a-ffe019e17758
-- title:
--   Dv: mul right
-- statement:
--   The Dv construction uses the mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L68-L70

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

theorem Formalism.HermitianLattices.Ext.L3.U0.Dv.mul_right {a : K} (ha : Dv S π a) {s : K} (hs : s ∈ S) : Dv S π (a * s) := by sorry
