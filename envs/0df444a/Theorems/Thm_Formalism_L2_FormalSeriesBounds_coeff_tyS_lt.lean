-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_lt
-- name    : Formalism.L2.FormalSeriesBounds.coeff_tyS_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:15.852898+00:00
-- url     : https://prove2.me/theorems/394fc4ac-f338-42e0-a077-294fd000ecec
-- title:
--   Formal Series Bounds: coeff ty S lt
-- statement:
--   The Formal Series Bounds construction uses the coeff ty S lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValNonnegLeadingCoeffOfMemTySet.lean#L90-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValNonnegLeadingCoeffOfMemTySet.lean#L90-L101

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.coeff_tyS_lt {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (s : ℕ) (ha : ∀ i < s, a i = 0) (m : ℕ) (hm : m < l ^ s) :
    PowerSeries.coeff m (tyS l a) = 0 := by sorry
