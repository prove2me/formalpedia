-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_quasiRefl_comp
-- name    : Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:52.223691+00:00
-- url     : https://prove2.me/theorems/703a128b-79cf-4ca2-bc1f-0412d82b04b0
-- title:
--   WA: quasi Refl comp
-- statement:
--   The WA construction uses the quasi Refl comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomFix.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomFix.lean#L19-L27

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by sorry
