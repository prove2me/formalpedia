-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LandL_gram_det_unit
-- name    : Formalism.HermitianLattices.Ext.L3.LandL.gram_det_unit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:44:05.192219+00:00
-- url     : https://prove2.me/theorems/e4a55300-93eb-52bd-bc5c-85b6103a3f7a
-- title:
--   Land L: gram det unit
-- statement:
--   The Land L construction uses the gram det unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandLA.lean#L17-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandLA.lean#L17-L60

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LandL

theorem Formalism.HermitianLattices.Ext.L3.LandL.gram_det_unit {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (A : Subring K) (hA : ∀ x ∈ A, star x ∈ A) (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
    (g : Basis (Fin n) K V)
    (hdual : ∀ x : V, (∀ y : V, (∀ i, g.repr y i ∈ A) → h y x ∈ A) ↔ ∀ i, g.repr x i ∈ A)
    (h0 : (gram h g).det ≠ 0) : (gram h g).det ∈ A ∧ ((gram h g).det)⁻¹ ∈ A := by sorry
