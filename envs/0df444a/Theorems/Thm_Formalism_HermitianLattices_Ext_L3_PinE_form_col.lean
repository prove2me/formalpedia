-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinE_form_col
-- name    : Formalism.HermitianLattices.Ext.L3.PinE.form_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:47.052065+00:00
-- url     : https://prove2.me/theorems/a272e8c7-43a1-4a43-9bb2-71507c84c430
-- title:
--   Pin E: form col
-- statement:
--   The Pin E construction uses the form col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L53-L56

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem Formalism.HermitianLattices.Ext.L3.PinE.form_col {H X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A} (hX : Xᴴ * H * X = H)
    (h00 : H (Sum.inl ()) (Sum.inl ()) = 1) : star (X *ᵥ e₀) ⬝ᵥ (H *ᵥ (X *ᵥ e₀)) = 1 := by sorry
