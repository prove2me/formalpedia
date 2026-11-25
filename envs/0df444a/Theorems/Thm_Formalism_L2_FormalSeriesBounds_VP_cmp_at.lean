-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cmp_at
-- name    : Formalism.L2.FormalSeriesBounds.VP.cmp_at
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:33.353293+00:00
-- url     : https://prove2.me/theorems/8dedb6cf-095c-5ee5-95fe-017749d6dc69
-- title:
--   VP: cmp at
-- statement:
--   The VP construction uses the cmp at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L90-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L90-L111

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.cmp_at {ε ε' : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hε' : ∀ i, MvPowerSeries.constantCoeff (ε' i) = 0) {a b : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    MvPowerSeries.subst (P2 a b) (FB.expS C (ev (n := 2) ![comp1 ε (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 ε' (pt C dd 1)] Y.h)) =
      mvExp (hAt Y (mapAt ε a) b - hAt Y a (mapAt ε' b)) := by sorry
