-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_alongCv_congr
-- name    : Formalism.L2.FormalSeriesBounds.coeff_alongCv_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:30.733847+00:00
-- url     : https://prove2.me/theorems/123c94cb-5470-4a5f-8ea2-e8dac3a24df3
-- title:
--   Formal Series Bounds: coeff along Cv congr
-- statement:
--   The Formal Series Bounds construction uses the coeff along Cv congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L14-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L14-L43

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
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

theorem Formalism.L2.FormalSeriesBounds.coeff_alongCv_congr {σ : Type} [Finite σ] {a a' : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, PowerSeries.constantCoeff (a' i) = 0) {k : ℕ}
    (h : ∀ i, ∀ m < k, PowerSeries.coeff m (a i) = PowerSeries.coeff m (a' i)) (f : MvPowerSeries σ C) :
    ∀ m < k, PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv a' f) := by sorry
