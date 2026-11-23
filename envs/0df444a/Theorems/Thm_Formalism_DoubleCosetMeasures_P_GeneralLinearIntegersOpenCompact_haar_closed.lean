-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_haar_closed
-- name    : Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.haar_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:24.875447+00:00
-- url     : https://prove2.me/theorems/3b21bdae-da38-4234-8b9f-83d05279c9b1
-- title:
--   General Linear Integers Open Compact: haar closed
-- statement:
--   The General Linear Integers Open Compact construction uses the haar closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L186-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L186-L234

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.haar_closed [T2Space K] (R : Subring K) (hRo : IsOpen (R : Set K))
    (hRc : IsCompact (R : Set K)) (ϖ : Kˣ) (hϖ : (ϖ : K) ∈ R)
    (hx : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) (hH : IsClosed (H : Set (GL (Fin n) K))) (e : Fin n → ℕ)
    (hstr : ∀ g ∈ H, ∀ a b, (g : Matrix (Fin n) (Fin n) K) a b = 0 ∨
      (a = b ∧ (g : Matrix (Fin n) (Fin n) K) a b = 1) ∨ e a < e b) :
    ∃ μ : Measure H, μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ SFinite μ ∧
      μ (intSub R H : Set H) = 1 := by sorry
