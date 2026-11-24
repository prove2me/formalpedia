-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_of_dv_mul
-- name    : Formalism.HermitianLattices.Ext.L3.U0.dv_of_dv_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:33.70411+00:00
-- url     : https://prove2.me/theorems/49e2f389-c709-4725-ab96-4c42f5c40135
-- title:
--   U0: dv of dv mul
-- statement:
--   The U0 construction uses the dv of dv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L150-L157

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

theorem Formalism.HermitianLattices.Ext.L3.U0.dv_of_dv_mul (hS : IsHermSemilocal S) (hπ : IsUnif S π) {a c : K} (hc : c ∈ S)
    (hn : ¬ Dv S π c) (h1 : Dv S π (a * c)) (h2 : Dv S π (star a * c)) : Dv S π a := by sorry
