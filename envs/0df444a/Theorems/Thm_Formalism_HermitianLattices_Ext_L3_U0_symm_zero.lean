-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_symm_zero
-- name    : Formalism.HermitianLattices.Ext.L3.U0.symm_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:12.412745+00:00
-- url     : https://prove2.me/theorems/883e32a9-a55b-4935-88b3-7a94500e86ca
-- title:
--   U0: symm zero
-- statement:
--   The U0 construction uses the symm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L25-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem Formalism.HermitianLattices.Ext.L3.U0.symm_zero (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by sorry
