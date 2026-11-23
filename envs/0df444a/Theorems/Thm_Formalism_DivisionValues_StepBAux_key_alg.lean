-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_key_alg
-- name    : Formalism.DivisionValues.StepBAux.key_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:54.266427+00:00
-- url     : https://prove2.me/theorems/654e1ee0-ae3f-452a-a821-8ed5ee400069
-- title:
--   Step BAux: key alg
-- statement:
--   The Step BAux construction uses the key alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L355-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L355-L373

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux

theorem Formalism.DivisionValues.StepBAux.key_alg {J : Type} [Fintype J] (D : ℕ) (gE0 gE1 dR0 dR1 G0 G1 Ny κ ρ : ℂ)
    (gW0 gW1 dθ0 dθ1 gT0 gT1 Nz : J → ℂ)
    (h1 : gE1 = Ny * gE0) (h21 : gE1 = dR1 * G1) (h20 : gE0 = dR0 * G0)
    (h31 : dR1 = (κ * ρ) ^ D * ∏ j, dθ1 j) (h30 : dR0 = κ ^ D * ∏ j, dθ0 j)
    (h4 : ∀ j, gW1 j = Nz j * gW0 j) (h51 : ∀ j, gW1 j = dθ1 j * gT1 j)
    (h50 : ∀ j, gW0 j = dθ0 j * gT0 j) (hκ : κ ≠ 0) (hθ : ∀ j, dθ0 j ≠ 0) :
    ρ ^ D * G1 * ∏ j, (Nz j * gT0 j) = Ny * G0 * ∏ j, gT1 j := by sorry
