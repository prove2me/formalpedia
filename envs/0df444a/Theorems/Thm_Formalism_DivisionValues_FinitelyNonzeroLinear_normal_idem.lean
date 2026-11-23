-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_normal_idem
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.normal_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:37.615911+00:00
-- url     : https://prove2.me/theorems/4a5879db-f291-4e40-bdfa-ca3c1d4da12a
-- title:
--   Finitely Nonzero Linear: normal idem
-- statement:
--   The Finitely Nonzero Linear construction uses the normal idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L29-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L29-L57

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
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
open Formalism.DivisionValues.FinitelyNonzeroLinear

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.normal_idem {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (M E : Matrix (Fin n) (Fin n) ℂ) (hM : M * M = M) (hadj : Mᴴ * Hc = Hc * E)
    (hc : E * M = M * E) : E = M := by sorry
