-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_dmap_zePart
-- name    : Formalism.L2.FormalSeriesBounds.dmap_zePart
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:54.699301+00:00
-- url     : https://prove2.me/theorems/9f5d7a6f-c1a5-43e4-b319-5830d2c0c093
-- title:
--   Formal Series Bounds: dmap ze Part
-- statement:
--   The Formal Series Bounds construction uses the dmap ze Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L118-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L118-L127

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem Formalism.L2.FormalSeriesBounds.dmap_zePart (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (ε : Pt C 1 dd) (s : Orb × Fin 2) (m : Fin dd) :
    ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • zePart Y p s j =
      ∑ c : I s.1 s.2, linAct ε ((p s.1).u s.2 c) m •
        (MvPowerSeries.X (⟨s.1, ⟨s.2, c⟩⟩ : WVO I) : MvPowerSeries (WVO I) C) := by sorry
