-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linPt_pl
-- name    : Formalism.L2.FormalSeriesBounds.VP.linPt_pl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:45.675309+00:00
-- url     : https://prove2.me/theorems/e4e25697-7cb8-509d-a11e-5b53f6912560
-- title:
--   VP: lin Pt pl
-- statement:
--   The VP construction uses the lin Pt pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L60-L72

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
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
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

theorem Formalism.L2.FormalSeriesBounds.VP.linPt_pl (ρ : Fin N) (col : Fin 2) (i : Fin dd) :
    linPt Y (MS Y p pl) (pl (ρ, col), i) = rowOf ρ (linPt Y (uS Y p) (col, i)) := by sorry
