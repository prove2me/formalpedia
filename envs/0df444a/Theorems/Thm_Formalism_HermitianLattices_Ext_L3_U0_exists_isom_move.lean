-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isom_move
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_isom_move
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:31.931012+00:00
-- url     : https://prove2.me/theorems/8164a3be-c54e-4fe3-b8cb-0bd999a542ee
-- title:
--   U0: exists isom move
-- statement:
--   The U0 construction uses the exists isom move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L100-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomScale.lean#L100-L157

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

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_isom_move (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {x y : V}
    (hxy : h x x = h y y) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by sorry
