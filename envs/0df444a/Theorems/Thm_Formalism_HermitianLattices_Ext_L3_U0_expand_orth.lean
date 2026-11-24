-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_expand_orth
-- name    : Formalism.HermitianLattices.Ext.L3.U0.expand_orth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:34.340706+00:00
-- url     : https://prove2.me/theorems/0e5e74b2-62ad-44fa-9ee3-2adf744eeecc
-- title:
--   U0: expand orth
-- statement:
--   The U0 construction uses the expand orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsASDOfTuple.lean#L37-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsASDOfTuple.lean#L37-L67

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
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
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.U0.expand_orth [FiniteDimensional K V] {y : Fin (finrank K V) → V}
    (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) (hne : ∀ i, h (y i) (y i) ≠ 0) (v : V) :
    v = ∑ i, (h (y i) v * (h (y i) (y i))⁻¹) • y i := by sorry
