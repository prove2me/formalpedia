-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_constantCoeff_pair_substitution
-- name    : Formalism.L2.FormalSeriesBounds.VP.constantCoeff_pair_substitution
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:13.812002+00:00
-- url     : https://prove2.me/theorems/659dc6d8-e122-5059-a123-be4c56a961c9
-- title:
--   VP: constant Coeff pair substitution
-- statement:
--   The VP construction uses the constant Coeff pair substitution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean#L22-L27

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.VP.constantCoeff_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff (P2 a b q) = 0 := by sorry
