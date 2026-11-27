-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_lgCv_agr
-- name    : Formalism.L2.FormalSeriesBounds.lgCv_agr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:13.153253+00:00
-- url     : https://prove2.me/theorems/830b3f4f-c6d6-5002-b252-b6cecb441e35
-- title:
--   Formal Series Bounds: lg Cv agr
-- statement:
--   The Formal Series Bounds construction uses the lg Cv agr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L187-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L187-L204

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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

theorem Formalism.L2.FormalSeriesBounds.lgCv_agr (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C}
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (i : Fin dd) :
    Agr (V.l ^ 2) (alongCv γ ((Y.raw p).lg i))
      ((∑ c, (Y.raw p).u g c i * w c) • (MvPowerSeries.X () : PowerSeries C)) := by sorry
