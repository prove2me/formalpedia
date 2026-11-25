-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_eq_map_invol
-- name    : Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.comap_eq_map_invol
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:24.431891+00:00
-- url     : https://prove2.me/theorems/971ce029-dd5e-4f3a-9b68-ee677c57439e
-- title:
--   Split Prime Ideals: comap eq map invol
-- statement:
--   The Split Prime Ideals construction uses the comap eq map invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L18-L24

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.comap_eq_map_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : P.comap σ = P.map σ := by sorry
