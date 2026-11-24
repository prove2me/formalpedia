-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_tele
-- name    : Formalism.FourierDecayAlt.P.JFxDs3.tele
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:33:14.468997+00:00
-- url     : https://prove2.me/theorems/95e1ec1e-9a97-48f4-915c-630691aacf83
-- title:
--   JFx Ds3: tele
-- statement:
--   The JFx Ds3 construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L25-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L25-L144

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxDs3.tele {F : Mat k r → E} {A c K ε : ℝ} {m : ℕ} (h : CCle A m F c) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (φ ψ : Bool × Mat k r → Bool × Mat k r) :
    ∀ (w pre : List (Bool × Mat k r)), (∀ x ∈ pre, inLie k r x.2 ∧ ‖x.2‖ ≤ K) →
      (∀ x ∈ w, (φ x).1 = x.1 ∧ (ψ x).1 = x.1 ∧ inLie k r (φ x).2 ∧ inLie k r (ψ x).2 ∧
        ‖(φ x).2‖ ≤ K ∧ ‖(ψ x).2‖ ≤ K ∧ ‖(φ x).2 - (ψ x).2‖ ≤ ε) →
      LRt ((pre ++ w).map Prod.fst) → (pre ++ w).length ≤ m → ∀ g ∈ GV k r,
      gN g ^ A * ‖W (pre ++ w.map φ) F g - W (pre ++ w.map ψ) F g‖ ≤ w.length * (K ^ m * ε * c) := by sorry
