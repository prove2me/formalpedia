-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_quot_core
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.quot_core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:51:35.393642+00:00
-- url     : https://prove2.me/theorems/bc8a6849-2ba1-49ab-9a2a-acce9f0aa2da
-- title:
--   BQuot: quot core
-- statement:
--   The BQuot construction uses the quot core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L157-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L157-L234

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem Formalism.LatticeBaseChangeAlt.BQuot.quot_core (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (c : V →ₗ[K] (Fin n → K))
    (N : Submodule K V) (hN : LinearMap.ker c ≤ N) (X : Submodule O V) (e be : ℕ)
    (th : Fin n → V)
    (hX : ∀ x ∈ X, ∀ i, ∃ a : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a)
    (hth : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X)
    (a a' : O) (ha : a ≠ 0)
    (hdet : algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a') :
    ql X ((X ⊓ N.restrictScalars O) ⊔
        Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) +
      IsDiscreteValuationRing.addVal O a' ≤
      IsDiscreteValuationRing.addVal O a + ((n * be : ℕ) : ℕ∞) := by sorry
