-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_mem_perpR
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_mem_perpR
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:36.228687+00:00
-- url     : https://prove2.me/theorems/aea715da-d1ca-47d2-b8bd-1fe777b90c75
-- title:
--   P: s5a4 mem perp R
-- statement:
--   The P construction uses the s5a4 mem perp R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L22-L25

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false

theorem Formalism.HermitianLatticeCounting.P.s5a4_mem_perpR {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
    (B : V →ₗ[K] V →ₛₗ[σ] K) (A : Submodule K V) (x : V) :
    x ∈ perpR B A ↔ ∀ a ∈ A, B a x = 0 := by sorry
