-- Prove2me | Theorems.Thm_Formalism_DivisionValues_lattice_gluing_semilocal
-- name    : Formalism.DivisionValues.lattice_gluing_semilocal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:27.954445+00:00
-- url     : https://prove2.me/theorems/8fbecfaf-1462-5631-8f16-5ff37ef15060
-- title:
--   Division Values: lattice gluing semilocal
-- statement:
--   The Division Values construction uses the lattice gluing semilocal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L294-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L294-L312

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open GluingInclusion Formalism.HermitianLatticesTheory

theorem Formalism.DivisionValues.lattice_gluing_semilocal : LatticeGlueSemi := by sorry
