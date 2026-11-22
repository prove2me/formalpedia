-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_left
-- name    : Formalism.HermitianLattices.Ext.L3.U0.Dv.mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:43.950121+00:00
-- url     : https://prove2.me/theorems/c4c21361-cbe2-4d39-9fdd-f7d99c14fb7c
-- title:
--   Dv: mul left
-- statement:
--   The Dv construction uses the mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L63-L66

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

theorem Formalism.HermitianLattices.Ext.L3.U0.Dv.mul_left {a : K} (ha : Dv S π a) {s : K} (hs : s ∈ S) : Dv S π (s * a) := by sorry
