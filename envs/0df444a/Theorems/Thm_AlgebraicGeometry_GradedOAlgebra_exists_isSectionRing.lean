-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
-- name    : AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/297a0e33-dac3-5241-9eca-2337b3cd7f32
-- title:
--   Existence of the section ring of an invertible module
-- statement:
--   Let $S$ be a commutative ring, let $X$ be a scheme, let $f : X \to \operatorname{Spec} S$ be a morphism of schemes, and let $L$ be an object of $X$-modules which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module on $U$. Then there exist a type $R$ carrying a commutative ring structure and an $S$-algebra structure, a family of $S$-submodules $\mathcal R_n \subseteq R$ indexed by $n \in \mathbb N$ making $R$ an internally graded $S$-algebra, and maps $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ into the global sections of the iterated tensor powers $L^{\otimes 0} = \mathbf 1$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$, such that `IsSectionRing` holds: each $\iota_n$ is bijective and additive; $\iota_n(s \cdot x) = \mathrm{baseScalar}(f)(s) \cdot \iota_n(x)$ for $s \in S$, where $\mathrm{baseScalar}(f)(s) \in \Gamma(X, \top)$ is the image of $s$ under $f^{\sharp}$ on global sections composed with the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism; $\iota_0$ sends the element $1$ of $\mathcal R_0$ to the section $1 \in \Gamma(X, \top)$ of the unit module; and for $x \in \mathcal R_m$, $y \in \mathcal R_n$ the section $\iota_{m+n}(xy)$ is the image of the tensor product section $\iota_m(x) \otimes \iota_n(y)$ under the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$ assembled from the unitor and associator.
--
--   This is the construction of the graded section ring $\bigoplus_{n \ge 0} \Gamma(X, L^{\otimes n})$ of an invertible module over an affine base, presented as an existence statement for a graded commutative $S$-algebra together with degreewise identifications with the section groups; commutativity of $R$ is part of the assertion and uses invertibility of $L$. It is used in the treatment of cocycle conditions for rigidified line bundles and in the descent statement for faithfully flat morphisms within the relative Picard functor development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra S R) (𝓡 : ℕ → Submodule S R) (_ : GradedAlgebra 𝓡)
      (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)), AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι := by sorry
