-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_finite_euler_quotient_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_finite_euler_quotient_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-11T12:20:31.340485+00:00
-- url     : https://prove2.me/theorems/175ea1dd-ba9d-4e6d-8299-e90cefb68694
-- title:
--   Finite Euler quotient for integer families of invertible sheaves on a proper scheme
-- statement:
--   Let $X$ be a proper scheme over an algebraically closed field $K$. Let $L$ be an abelian group, regarded as a module over $\mathbb Z$, and let $\ell_x$ be invertible sheaves on $X$ whose isomorphism classes define a homomorphism from $L$ to the tensor monoid of sheaf isomorphism classes.
--
--   There exist a finitely generated abelian group $A$ and a surjective homomorphism
--
--   $$q:L\longrightarrow A$$
--
--   such that, whenever $q(x)=q(y)$, every closed immersion $f:Y\hookrightarrow X$ satisfies
--
--   $$\chi(Y,f^*\ell_x)=\chi(Y,f^*\ell_y).$$
--
--   Here Euler characteristic is computed from the actual cohomology of the invertible sheaf; in the formal statement it is expressed using any ordered affine cover of $Y$. The same quotient works for all closed subschemes and all twists in $L$. No smoothness, integrality, connectedness, or finite-generation assumption on $L$ is imposed.
--
--   This is a numerical consequence of Néron–Severi finite generation and constancy of Euler characteristic under algebraic equivalence. It isolates a general geometric input for constructions involving infinitely many translated line bundles. It is a consequence of the cited results, not a literal transcription of a single source theorem.
--
--   **Formalization Note.** The finitely generated quotient is represented in universe zero; no rank bound or choice of generators is prescribed.
-- source:
--   SGA 6, Exposé XIII, Théorème 5.1, printed p. 650 (PDF p. 653), https://library.slmath.org/nonmsri/sga/sga/pdf/sga6.pdf; Stacks Project, Lemma 36.32.2, https://stacks.math.columbia.edu/tag/0B9T. The assertion is the joint consequence described in the statement.

import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_finite_euler_quotient_of_isProper
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (L : Type u) [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∀ (Y : Scheme.{u}) (f : Y ⟶ X), IsClosedImmersion f →
        ∀ U : Y.OrderedAffineCover,
          (OModulePresheaf.ofModules (f ≫ π) ((Scheme.Modules.pullback f).obj (ℓ x))).eulerChar U =
          (OModulePresheaf.ofModules (f ≫ π) ((Scheme.Modules.pullback f).obj (ℓ y))).eulerChar U := by sorry
