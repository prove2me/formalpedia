-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_iter
-- name    : Formalism.L2.FormalSeriesBounds.VP.jet_iter
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:26.28362+00:00
-- url     : https://prove2.me/theorems/6ba3a7b6-fe41-4574-914a-5ed7a5802237
-- title:
--   VP: jet iter
-- statement:
--   The VP construction uses the jet iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L58-L70

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
variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

theorem Formalism.L2.FormalSeriesBounds.VP.jet_iter (hD : DPullSt Y p) {n : ℕ} (b : Fin n) (u : Fin dd → C) (c : WVO I → C)
    (hu : u = ∑ w : WVO I, c w • (Y.raw (p w.1)).u w.2.1 w.2.2) (k : ℕ) :
    ∀ (q : MvPolynomial (Fin n × WVO I) C) (g : PS C n dd),
      jetAt0 q (pullN Y p ((DofN (Y.B.FK C) b u)^[k] g)) =
        jetAt0 (q * (∑ w : WVO I, MvPolynomial.C (c w) * MvPolynomial.X (b, w)) ^ k) (pullN Y p g) := by sorry
