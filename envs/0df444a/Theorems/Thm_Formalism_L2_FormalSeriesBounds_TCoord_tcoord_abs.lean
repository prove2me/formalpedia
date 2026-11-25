-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_TCoord_tcoord_abs
-- name    : Formalism.L2.FormalSeriesBounds.TCoord.tcoord_abs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:26.659153+00:00
-- url     : https://prove2.me/theorems/50abbcda-9f24-53ad-bdda-427e57994419
-- title:
--   TCoord: tcoord abs
-- statement:
--   The TCoord construction uses the tcoord abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieP_TCoord.lean#L16-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieP_TCoord.lean#L16-L113

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieP_TCoord
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
open Formalism.L2.FormalSeriesBounds.TCoord
open Formalism.IncomingBounds FormalGermZero GeneralGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]

theorem Formalism.L2.FormalSeriesBounds.TCoord.tcoord_abs {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ) (g : Fin 2)
    (w : κ → I g → C) (hwI : ∀ x c, V.Ge 0 (w x c))
    (hw : ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (tan : I g → I g → C) (hun : V.v (Matrix.of tan).det = 0)
    (P : κ → MvPowerSeries (I g) C) (hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0) (hPI : ∀ j, IntS V (P j))
    (hPlin : ∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * tan c c')
    (t : I g → MvPowerSeries (I g) C) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hPt : ∀ j, MvPowerSeries.subst t (P j) =
      MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j))
    (c : I g) :
    ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t c) := by sorry
