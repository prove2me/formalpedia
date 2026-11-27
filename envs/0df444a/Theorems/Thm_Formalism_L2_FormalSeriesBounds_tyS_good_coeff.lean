-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_good_coeff
-- name    : Formalism.L2.FormalSeriesBounds.tyS_good_coeff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:38.944181+00:00
-- url     : https://prove2.me/theorems/714e6ea3-5ab2-45d9-8e1c-23e6a5f27f77
-- title:
--   Formal Series Bounds: ty S good coeff
-- statement:
--   The Formal Series Bounds construction uses the ty S good coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L158-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L158-L182

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem Formalism.L2.FormalSeriesBounds.tyS_good_coeff {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (hl : 2 ≤ V.l) (c : I g) (n : ℕ)
    (hn : n < V.l ^ 2) :
    PowerSeries.coeff n (tyS V.l (fun s => x s (Sum.inl c))) = if n = 1 then w c else 0 := by sorry
