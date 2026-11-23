-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_lower_pk
-- name    : Formalism.FourierDecayAlt.P.HLsc.lower_pk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:05.760871+00:00
-- url     : https://prove2.me/theorems/0b9f3321-71c2-40bc-9ccf-0cd38891cf5a
-- title:
--   HLsc: lower pk
-- statement:
--   The HLsc construction uses the lower pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L340-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L340-L418

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.HLsc.lower_pk {N : (Fin d → ℝ) → ℝ} (hN0 : ∀ z, 0 ≤ N z) (hint : Integrable N)
    (z₀ : Fin d → ℝ) (S : Finset (Fin d → ℤ)) (η : ℝ) (U : Set (Fin d → ℝ)) (hUo : IsOpen U)
    (hU1 : ∀ y ∈ U, ∀ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) - η < N (fun j => z₀ j + (m j : ℝ) + y j))
    (hU2 : ∀ y ∈ U, ∀ j, |y j| < 1 / 2) (n : ℕ) :
    (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η)) *
      (∫ y in cube d, pk y ^ n • U.indicator (fun _ => (1 : ℝ)) y) ≤ ∫ z, N z * pk (z - z₀) ^ n := by sorry
