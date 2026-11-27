-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_hom_of_good
-- name    : Formalism.L2.FormalSeriesBounds.hom_of_good
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T05:14:35.344815+00:00
-- url     : https://prove2.me/theorems/089c1a2e-a40c-5b0a-8ccb-588e988f03c5
-- title:
--   Formal Series Bounds: hom of good
-- statement:
--   The Formal Series Bounds construction uses the hom of good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L239-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L239-L305

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
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

theorem Formalism.L2.FormalSeriesBounds.hom_of_good (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (i : Fin dd) (μ : Fin 2 →₀ ℕ) (hμ0 : μ 0 < V.l) (hμ1 : μ 1 < V.l) :
    MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)) = 0 := by sorry
