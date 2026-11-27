-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff1_of_good
-- name    : Formalism.L2.FormalSeriesBounds.coeff1_of_good
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:20.789809+00:00
-- url     : https://prove2.me/theorems/89ef16ff-cc55-5163-9d89-8ae3fa280917
-- title:
--   Formal Series Bounds: coeff1 of good
-- statement:
--   The Formal Series Bounds construction uses the coeff1 of good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L307-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L307-L321

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

theorem Formalism.L2.FormalSeriesBounds.coeff1_of_good (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (i : Fin dd) : PowerSeries.coeff 1 (γ i) = ∑ c, (Y.raw p).u g c i * w c := by sorry
