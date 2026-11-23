-- Prove2me | Theorems.Thm_Formalism_L2_DIV_hform_smul
-- name    : Formalism.L2.DIV.hform_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:23.505802+00:00
-- url     : https://prove2.me/theorems/b6cb6f67-a808-450c-aecb-18925e981b96
-- title:
--   DIV: hform smul
-- statement:
--   The DIV construction uses the hform smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1174-L1179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1174-L1179

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues

theorem Formalism.L2.DIV.hform_smul {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (c : K)
    (H : Matrix (Fin n) (Fin n) K) (y x : Fin n → K) : hform (c • H) y x = hform H y (c • x) := by sorry
