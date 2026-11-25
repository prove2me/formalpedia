-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_expS_bil
-- name    : Formalism.L2.FormalSeriesBounds.coeff_expS_bil
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:40.259673+00:00
-- url     : https://prove2.me/theorems/9287aae4-d5ae-4e56-b90d-c51454770b4c
-- title:
--   Formal Series Bounds: coeff exp S bil
-- statement:
--   The Formal Series Bounds construction uses the coeff exp S bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L248-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L248-L260

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {n dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.coeff_expS_bil {T : Set (Fin n × Fin dd)} {f : PS C n dd} (hf : Van T f) (e : Fin n × Fin dd →₀ ℕ)
    (P : Fin n × Fin dd) (he : ∀ s ∈ T, e s ≠ 0 → s = P) (hP : e P ≤ 1) (he0 : e ≠ 0) :
    coeff e (FB.expS C f) = coeff e f := by sorry
