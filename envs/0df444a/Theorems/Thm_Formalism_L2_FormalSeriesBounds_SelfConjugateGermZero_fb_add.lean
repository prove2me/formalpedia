-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_fb_add
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.fb_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:44.763968+00:00
-- url     : https://prove2.me/theorems/e4868ced-e544-43fa-8a81-7faf99daf715
-- title:
--   Self Conjugate Germ Zero: fb add
-- statement:
--   The Self Conjugate Germ Zero construction uses the fb add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L114-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L114-L141

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.fb_add (Y : FBChart C V O dd) (j : Fin dd) :
    MvPowerSeries.subst Y.B.G.F (un1 (Y.lg j)) =
      MvPowerSeries.subst (fun q : Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun q : Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.lg j)) := by sorry
