-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_lin
-- name    : Formalism.L2.FormalSeriesBounds.VP.jet_lin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:37:00.959999+00:00
-- url     : https://prove2.me/theorems/2c69d96a-f379-5b33-a074-5cc75a79c34e
-- title:
--   VP: jet lin
-- statement:
--   The VP construction uses the jet lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L49-L54

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
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
open Formalism.L2.FormalSeriesBounds.VP

theorem Formalism.L2.FormalSeriesBounds.VP.jet_lin {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv C (e w) G) := by sorry
