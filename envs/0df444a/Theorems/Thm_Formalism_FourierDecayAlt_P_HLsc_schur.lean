-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_schur
-- name    : Formalism.FourierDecayAlt.P.HLsc.schur
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:29.023039+00:00
-- url     : https://prove2.me/theorems/b7980c6f-3f78-457c-b2f1-688478050295
-- title:
--   HLsc: schur
-- statement:
--   The HLsc construction uses the schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L72-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L72-L97

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

theorem Formalism.FourierDecayAlt.P.HLsc.schur {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℝ) :
    ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * a σ * a σ' ≤ (∑' τ, κ τ) * ∑ σ ∈ B, a σ ^ 2 := by sorry
