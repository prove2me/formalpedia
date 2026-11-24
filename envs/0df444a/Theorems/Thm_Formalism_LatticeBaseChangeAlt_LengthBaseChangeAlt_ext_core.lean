-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LengthBaseChangeAlt_ext_core
-- name    : Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt.ext_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:52.137932+00:00
-- url     : https://prove2.me/theorems/12d2c93f-b2c8-49e5-ba65-c366d5410621
-- title:
--   Length Base Change Alt: ext core
-- statement:
--   The Length Base Change Alt construction uses the ext core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean#L85-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean#L85-L284

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
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
open Module TensorProduct
open Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
open BQuot
variable {O K K₁ V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
  [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt.ext_core (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (c : V →ₗ[K] (Fin n → K₁))
    (N : Submodule K V) (hN : LinearMap.ker c ≤ N) (th : Fin n → V)
    (hspan : LinearMap.ker c ⊔ Submodule.span K (Set.range th) = ⊤)
    (X : Submodule O V) (e be : ℕ)
    (hX : ∀ x ∈ X, ∀ i, ∃ y ∈ integralClosure O K₁,
        c x i = (algebraMap O K₁ ϖ) ^ ((e : ℤ) - (be : ℤ)) * y)
    (hth : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X)
    (a a' : O) (ha : a ≠ 0)
    (hdet : algebraMap O K a =
      Algebra.norm K (Matrix.of fun i j => c (th j) i).det * algebraMap O K a') :
    (finrank K K₁ : ℕ∞) * ql X ((X ⊓ N.restrictScalars O) ⊔
        Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) +
      IsDiscreteValuationRing.addVal O a' ≤
      IsDiscreteValuationRing.addVal O a + ((finrank K K₁ * n * be : ℕ) : ℕ∞) := by sorry
