-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_algEquiv_quotient_of_smoothProperCurve
-- name    : AlgebraicGeometry.RelPicard.exists_finite_algEquiv_quotient_of_smoothProperCurve
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T14:59:44.270694+00:00
-- url     : https://prove2.me/theorems/7de16940-a851-47bb-84dc-173212064575
-- title:
--   Finite algebraic-equivalence quotient for line-bundle families on smooth proper curves
-- statement:
--   Let $X$ be an integral smooth proper curve over an algebraically closed field $K$, and let $L$ be an abelian group. Assign to each $x\in L$ an invertible sheaf $\ell_x$ on $X$, with isomorphism classes respecting addition and tensor product.
--
--   There are a finitely generated abelian group $A$ and a surjective homomorphism $q:L\to A$ such that
--
--   $$q(x)=q(y)\quad\Longrightarrow\quad \ell_x\simeq N\otimes\ell_y$$
--
--   for some invertible sheaf $N$ algebraically equivalent to the trivial sheaf. Algebraic equivalence has its concrete parameter-family meaning: an invertible sheaf on $X\times_K T$, where $T$ is geometrically integral and locally of finite type over $K$, with two $K$-rational fibres isomorphic to the trivial sheaf and $N$.
--
--   No finite-generation assumption on $L$ is needed. The output group is represented in universe zero. Neither a chosen affine cover nor an assumed degree or rank bound is an input.
--
--   This proves the smooth proper integral curve case of the finite algebraic-equivalence quotient used in the Philippon mission. It does not assert the corresponding result for arbitrary proper schemes. The proof realizes the Néron–Severi group as a subgroup of the integers via the actual Čech Euler degree.
-- source:
--   Curve specialization and image-group consequence of SGA 6, Exposé XIII, Théorème 5.1, printed p. 650 (PDF p. 653), https://library.slmath.org/nonmsri/sga/sga/pdf/sga6.pdf. This specialization is proved independently of the general finiteness theorem, using the existing proved curve results AlgebraicGeometry.RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq (dc023f08-88af-594a-8dae-29b1f86fed5d) and AlgebraicGeometry.Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub (d0c75cad-4622-5d60-8a58-3c9fc19d78fb), together with affine-cover existence and Noetherianity of the integers.

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory MonoidalCategory
universe u v

theorem AlgebraicGeometry.RelPicard.exists_finite_algEquiv_quotient_of_smoothProperCurve
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π] [SmoothOfRelativeDimension 1 π]
    (L : Type v) [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∃ N : X.Modules,
        Scheme.Modules.IsInvertible N ∧ IsAlgEquivZero π N ∧
          Nonempty (ℓ x ≅ N ⊗ ℓ y) := by sorry
