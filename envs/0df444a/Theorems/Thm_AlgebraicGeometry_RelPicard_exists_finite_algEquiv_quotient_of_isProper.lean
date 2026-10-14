-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_algEquiv_quotient_of_isProper
-- name    : AlgebraicGeometry.RelPicard.exists_finite_algEquiv_quotient_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-11T13:42:35.001451+00:00
-- url     : https://prove2.me/theorems/a6133d20-8dd4-4e78-a50e-01542e5046fa
-- title:
--   Finite algebraic-equivalence quotient for integer families of invertible sheaves
-- statement:
--   Let $X$ be a proper scheme over an algebraically closed field $K$, and let $L$ be any abelian group. Suppose invertible sheaves $\ell_x$ on $X$ are assigned to $x\in L$ so that their isomorphism classes respect addition and tensor product.
--
--   There are a finitely generated abelian group $A$ and a surjective homomorphism $q:L\to A$ such that, whenever $q(x)=q(y)$, there is an invertible sheaf $N$ algebraically equivalent to the trivial sheaf with
--
--   $$\ell_x\simeq N\otimes\ell_y.$$
--
--   Algebraic equivalence here has its existing concrete meaning: an invertible sheaf on $X\times_K T$ for a geometrically integral locally finite-type parameter scheme $T$, with two $K$-rational fibres isomorphic to the trivial sheaf and $N$.
--
--   This is the image form of Néron–Severi finite generation: take the image of $L$ in $\operatorname{Pic}(X)/\operatorname{Pic}^0(X)$. A subgroup of a finitely generated abelian group is finitely generated. Equality of classes yields the displayed algebraically trivial difference. No smoothness, integrality, or connectedness of $X$ is assumed, and $L$ need not be finitely generated. The finite quotient is represented in universe zero in the formal statement.
--
--   This statement contains no Euler-characteristic or numerical-rank premise. It is a consequence of the cited finiteness theorem and the usual parameter-family characterization of algebraic equivalence, rather than a literal transcription of the source theorem.
-- source:
--   SGA 6, Exposé XIII, Théorème 5.1, printed p. 650 (PDF p. 653), https://library.slmath.org/nonmsri/sga/sga/pdf/sga6.pdf. Specialize to an algebraically closed field, pass to the image subgroup, and express Picard-zero membership using the existing algebraic-equivalence family definition.

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem AlgebraicGeometry.RelPicard.exists_finite_algEquiv_quotient_of_isProper
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (L : Type u) [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∃ N : X.Modules,
        Scheme.Modules.IsInvertible N ∧ RelPicard.IsAlgEquivZero π N ∧
          Nonempty (ℓ x ≅ N ⊗ ℓ y) := by
  sorry
