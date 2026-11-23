-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_single
-- name    : Formalism.DivisionValues.RationalHermitianForm.hform_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:47.851526+00:00
-- url     : https://prove2.me/theorems/d31d9f57-bf9f-46d2-8a40-00683f6c3aad
-- title:
--   Rational Hermitian Form: hform single
-- statement:
--   The Rational Hermitian Form construction uses the hform single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/RatHerm.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/RatHerm.lean#L34-L42

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

theorem Formalism.DivisionValues.RationalHermitianForm.hform_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (i : Fin n) (y : Fin n → K) :
    hform H (Pi.single i 1) y = (H *ᵥ y) i := by sorry
