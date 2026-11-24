-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BesselUnitaryEquiv_integral_transfer
-- name    : Formalism.QuantumDeterminants.BesselUnitaryEquiv.integral_transfer
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:18.217812+00:00
-- url     : https://prove2.me/theorems/cf59ebc5-bfb6-41ee-b7b1-9cb684f2de3e
-- title:
--   Bessel Unitary Equiv: integral transfer
-- statement:
--   The Bessel Unitary Equiv construction uses the integral transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnitaryEquivHolds.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnitaryEquivHolds.lean#L60-L67

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BesselUnitaryEquiv
variable {k r : ℕ}

theorem Formalism.QuantumDeterminants.BesselUnitaryEquiv.integral_transfer {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    (f : α → α) (hf : MeasurePreserving f μ μ) (hfe : MeasurableEmbedding f)
    (L : E ≃L[ℂ] F) (I₀ : α → E) (I₁ : α → F)
    (h : ∀ᵐ p ∂μ, I₁ (f p) = L (I₀ p)) : ∫ p, I₁ p ∂μ = L (∫ p, I₀ p ∂μ) := by sorry
