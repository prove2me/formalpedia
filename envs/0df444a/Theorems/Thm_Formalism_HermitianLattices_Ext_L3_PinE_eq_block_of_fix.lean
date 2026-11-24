-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinE_eq_block_of_fix
-- name    : Formalism.HermitianLattices.Ext.L3.PinE.eq_block_of_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:58.998273+00:00
-- url     : https://prove2.me/theorems/4ebe870a-0d25-4994-a846-42b8cedd219b
-- title:
--   Pin E: eq block of fix
-- statement:
--   The Pin E construction uses the eq block of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L25-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L25-L51

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

theorem Formalism.HermitianLattices.Ext.L3.PinE.eq_block_of_fix {H' : Matrix κ κ A} {Y : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A}
    (hY : Yᴴ * HH H' * Y = HH H') (h0 : Y *ᵥ e₀ = e₀) :
    Y.toBlocks₂₂ᴴ * H' * Y.toBlocks₂₂ = H' ∧ Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by sorry
