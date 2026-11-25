-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_constantCoeff_single_point_zero
-- name    : Formalism.L2.FormalSeriesBounds.VP.constantCoeff_single_point_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:16:03.420006+00:00
-- url     : https://prove2.me/theorems/8525ef87-7032-548e-b47e-6ae43b9a38d0
-- title:
--   VP: constant Coeff single point zero
-- statement:
--   The VP construction uses the constant Coeff single point zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L63-L65

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem Formalism.L2.FormalSeriesBounds.VP.constantCoeff_single_point_zero {n : ℕ} (b : Fin n) (q : Fin 1 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2) = 0 := by sorry
