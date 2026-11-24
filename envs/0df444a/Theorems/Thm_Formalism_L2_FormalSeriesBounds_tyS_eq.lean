-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_eq
-- name    : Formalism.L2.FormalSeriesBounds.tyS_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:19:19.644579+00:00
-- url     : https://prove2.me/theorems/e5ef6251-792a-4bcc-a565-4c5985a7e601
-- title:
--   Formal Series Bounds: ty S eq
-- statement:
--   The Formal Series Bounds construction uses the ty S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L35-L42

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
variable {l : ℕ} (hl : 2 ≤ l)
include hl

theorem Formalism.L2.FormalSeriesBounds.tyS_eq (a : ℕ → C) (f : PowerSeries C) (h1 : ∀ s, PowerSeries.coeff (l ^ s) f = a s)
    (h2 : ∀ m, (∀ s, l ^ s ≠ m) → PowerSeries.coeff m f = 0) : tyS l a = f := by sorry
