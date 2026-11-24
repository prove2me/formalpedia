-- Prove2me | Theorems.Thm_Formalism_L2_DIV_convA
-- name    : Formalism.L2.DIV.convA
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:23.111801+00:00
-- url     : https://prove2.me/theorems/53024acf-1b22-4102-a432-7e22cc355e58
-- title:
--   DIV: conv A
-- statement:
--   The DIV construction uses the conv A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L822-L848
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L822-L848

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

theorem Formalism.L2.DIV.convA {k V G : Type} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] (φ : G → k)
    (hφ : ∀ g s, φ (g * s * g⁻¹) = φ s) (u : G) :
    (∑ s, φ s * ρ.character (s * u)) * (finrank k V : k) = (∑ s, φ s * ρ.character s) * ρ.character u := by sorry
