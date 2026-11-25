-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_curve_eq_ex_lg
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.curve_eq_ex_lg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:15.768108+00:00
-- url     : https://prove2.me/theorems/124c0a6c-5966-4631-961f-bb461c3a55b5
-- title:
--   Raw Chart: curve eq ex lg
-- statement:
--   The Raw Chart construction uses the curve eq ex lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L68-L75

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem Formalism.L2.FormalSeriesBounds.RawChart.curve_eq_ex_lg (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (δ : κ → PowerSeries C) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) (i : κ) :
    δ i = alongCv (fun j => alongCv δ (X.lg j)) (X.ex i) := by sorry
