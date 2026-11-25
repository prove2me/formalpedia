-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_lg_inj
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.lg_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:31.925805+00:00
-- url     : https://prove2.me/theorems/241de70f-8083-4215-b215-f18ef2f3eb17
-- title:
--   Raw Chart: lg inj
-- statement:
--   The Raw Chart construction uses the lg inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L158-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L158-L173

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
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

theorem Formalism.L2.FormalSeriesBounds.RawChart.lg_inj (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {γ γ' : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ' : ∀ i, PowerSeries.constantCoeff (γ' i) = 0)
    (h : ∀ i, alongCv γ (X.lg i) = alongCv γ' (X.lg i)) : γ = γ' := by sorry
