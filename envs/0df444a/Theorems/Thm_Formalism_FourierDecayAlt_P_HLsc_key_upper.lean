-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_key_upper
-- name    : Formalism.FourierDecayAlt.P.HLsc.key_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:52.029822+00:00
-- url     : https://prove2.me/theorems/303a950f-9672-4677-914d-85b428f79a21
-- title:
--   HLsc: key upper
-- statement:
--   The HLsc construction uses the key upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L99-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L99-L125

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

theorem Formalism.FourierDecayAlt.P.HLsc.key_upper {N : (Fin d → ℝ) → ℝ} {A : (Fin d → ℤ) → ℂ} (hint : Integrable N)
    (hPD : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re)
    (hsum : Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖))
    (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∫ z, N z * ‖tp B c z‖ ^ 2 ≤
      (∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) * ∑ σ ∈ B, ‖c σ‖ ^ 2 := by sorry
