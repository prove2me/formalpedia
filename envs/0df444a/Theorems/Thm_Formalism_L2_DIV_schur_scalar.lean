-- Prove2me | Theorems.Thm_Formalism_L2_DIV_schur_scalar
-- name    : Formalism.L2.DIV.schur_scalar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:58.432221+00:00
-- url     : https://prove2.me/theorems/a10edb00-5bb5-42ce-b444-3e09ccac3552
-- title:
--   DIV: schur scalar
-- statement:
--   The DIV construction uses the schur scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L812-L820
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L812-L820

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
open Representation

theorem Formalism.L2.DIV.schur_scalar {k V G : Type} [Field k] [IsAlgClosed k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] (T : V →ₗ[k] V)
    (hT : ∀ g v, T (ρ g v) = ρ g (T v)) : ∃ c : k, T = c • LinearMap.id := by sorry
