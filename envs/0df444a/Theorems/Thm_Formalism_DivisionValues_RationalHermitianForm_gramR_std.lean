-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_gramR_std
-- name    : Formalism.DivisionValues.RationalHermitianForm.gramR_std
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:12.741861+00:00
-- url     : https://prove2.me/theorems/3dd07821-9287-42df-9370-7dbb9a471512
-- title:
--   Rational Hermitian Form: gram R std
-- statement:
--   The Rational Hermitian Form construction uses the gram R std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/RatHerm.lean#L108-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/RatHerm.lean#L108-L118

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
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
open Formalism.DivisionValues.RationalHermitianForm
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.RationalHermitianForm.gramR_std {D : ℕ} (Γ : Matrix (Fin D) (Fin D) K) :
    gramR Γ (fun i => (Pi.single i 1 : Fin D → K)) = Γ.det := by sorry
