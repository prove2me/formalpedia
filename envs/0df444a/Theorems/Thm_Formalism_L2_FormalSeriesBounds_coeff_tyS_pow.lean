-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
-- name    : Formalism.L2.FormalSeriesBounds.coeff_tyS_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:19:31.694982+00:00
-- url     : https://prove2.me/theorems/ac489371-f3ff-4336-a482-f135b894a261
-- title:
--   Formal Series Bounds: coeff ty S pow
-- statement:
--   The Formal Series Bounds construction uses the coeff ty S pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L20-L27

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

theorem Formalism.L2.FormalSeriesBounds.coeff_tyS_pow (a : ℕ → C) (s : ℕ) : PowerSeries.coeff (l ^ s) (tyS l a) = a s := by sorry
