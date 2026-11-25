-- Prove2me | Theorems.Thm_AlgebraicGeometry_GrpObj_isSeparable_of_tangentMap_injective
-- name    : AlgebraicGeometry.GrpObj.isSeparable_of_tangentMap_injective
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:28:33.733124+00:00
-- url     : https://prove2.me/theorems/423130c9-be77-5220-8a3d-7b8f60aea7ea
-- title:
--   Separability criterion for isogenies: if the tangent map at the identity is injective, the endomorphism is a separable isogeny whose degree is the number of kernel points
-- statement:
--   Let $k$ be an algebraically closed field and let $A$ be a group scheme over $k$ whose structure morphism $A \to \operatorname{Spec} k$ is proper and whose underlying scheme is integral (for example an abelian variety), with identity section $e \in A(k)$. Let $k[\varepsilon] = k[X]/(X^2)$ be the ring of dual numbers and $\iota_0 \colon \operatorname{Spec} k \to \operatorname{Spec} k[\varepsilon]$ its closed point, given by $a + b\varepsilon \mapsto a$. A *tangent vector* to $A$ at $e$ is a morphism of $k$-schemes $t \colon \operatorname{Spec} k[\varepsilon] \to A$ with $t \circ \iota_0 = e$; these form the tangent space $T_eA$. An endomorphism of group schemes $\varphi \colon A \to A$ over $k$ has the tangent map $d\varphi \colon T_eA \to T_eA$, $t \mapsto \varphi \circ t$.
--
--   Suppose that $d\varphi$ is injective. Then $\varphi$ is dominant, its kernel $\ker\varphi(k) = \{c \in A(k) : \varphi(c) = e\}$ is finite, and, writing $K(A)$ for the function field of $A$ and $\eta$ for its generic point (so that $\varphi(\eta) = \eta$), the extension $K(A)/\varphi^* K(A)$ given by pull-back of rational functions along $\varphi$ is separable, of degree
--
--   $$\deg\varphi = [K(A) : \varphi^* K(A)] = \#\ker\varphi(k).$$
--
--   This is the separability criterion for isogenies. Since $T_eA$ is a finite-dimensional $k$-vector space and $d\varphi$ is $k$-linear, injectivity means that $d\varphi$ is bijective, and such an isogeny is separable, with every fibre over a $k$-point consisting of exactly $\deg\varphi$ points. For instance, for a commutative $A$ one has $d(\varphi + \psi) = d\varphi + d\psi$, so multiplication by an integer $n$ not divisible by the characteristic $p$ of $k$ has $d[n] = n$ invertible and is separable of degree $\#A[n](k)$. Likewise, for the $q$-power Frobenius endomorphism $\pi$ of an abelian variety defined over $\mathbb F_q$ one has $d\pi = 0$, so $d(F(\pi)) = F(0)$ for every $F \in \mathbb Z[X]$, and $F(\pi)$ is separable of degree $\#\ker F(\pi)(k)$ whenever $p \nmid F(0)$; for $F = 1 - X$ this gives $\deg(1 - \pi) = \#A(\mathbb F_q)$, the starting point for counting points through the characteristic polynomial of Frobenius.
--
--   **Formalization Note**: A group scheme over $k$ is `A : Over (Spec (.of k))` with `GrpObj A` for the cartesian monoidal structure of `Over (Spec k)` (the product is the fibre product over $k$); `A.left` is the scheme and `A.hom` its structure morphism. Endomorphisms of group schemes over $k$ are morphisms `φ : A ⟶ A` in `Over (Spec k)` with `IsMonHom φ`, and `t ≫ φ` is $\varphi \circ t$. The $k$-scheme $\operatorname{Spec} k[\varepsilon]$ is `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))` and $\operatorname{Spec} k$ over itself is the monoidal unit `𝟙_ (Over (Spec (.of k)))`. The closed point $\iota_0$ is given as a variable `ι₀` with the defining hypothesis `hι₀`: its underlying morphism of schemes is `Spec.map` of `TrivSqZeroExt.fstHom k k k` ($a + b\varepsilon \mapsto a$). A morphism in `Over` is determined by its underlying morphism, so `ι₀` is uniquely determined (and it exists). Morphisms into the group object `A` form a group (the `MonObj` hom-monoid, available after `open MonObj`) whose unit `1` factors through the identity section; so `ι₀ ≫ t = 1` says that $t$ is a tangent vector at $e$, and the hypothesis `hφ` says exactly that $t \mapsto \varphi \circ t$ is injective on tangent vectors. The $k$-points of $A$ are the sections `c : 𝟙_ (Over (Spec (.of k))) ⟶ A`, and the kernel is the subtype `{c // c ≫ φ = 1}`, asserted to be `Finite` and counted by `Nat.card`. The function field `A.left.functionField` is the stalk at the generic point; given `h : φ.left (genericPoint A.left) = genericPoint A.left`, the pull-back $\varphi^*$ is the stalk map of `φ.left` at the generic point preceded by the identification `stalkSpecializes (specializes_of_eq h)` of the stalk at $\eta$ with the stalk at $\varphi(\eta)$. Because `A.left.functionField` is also an algebra over itself through the identity, the algebra structure given by $\varphi^*$ is passed explicitly with `.toAlgebra`: `Algebra.IsSeparable` and `Module.finrank` refer to $K(A)$ as an algebra over itself via $\varphi^*$.
-- source:
--   D. Mumford, Abelian Varieties, Tata Institute of Fundamental Research Studies in Mathematics 5 (1970), Sections 4 and 7; J. S. Milne, Abelian Varieties (version 2.00, 2008), Part I, Section 7 (Isogenies)

import Mathlib

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

theorem AlgebraicGeometry.GrpObj.isSeparable_of_tangentMap_injective
    (k : Type) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [IsIntegral A.left]
    (ι₀ : 𝟙_ (Over (Spec (.of k))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))))
    (hι₀ : ι₀.left = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))
    (φ : A ⟶ A) [IsMonHom φ]
    (hφ : ∀ t s : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ A,
      ι₀ ≫ t = 1 → ι₀ ≫ s = 1 → t ≫ φ = s ≫ φ → t = s) :
    IsDominant φ.left ∧ Finite {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1} ∧
      ∃ h : φ.left (genericPoint A.left) = genericPoint A.left,
        @Algebra.IsSeparable A.left.functionField A.left.functionField _ _
          (A.left.presheaf.stalkSpecializes (specializes_of_eq h) ≫
            φ.left.stalkMap (genericPoint A.left)).hom.toAlgebra ∧
        @Module.finrank A.left.functionField A.left.functionField _ _
          (A.left.presheaf.stalkSpecializes (specializes_of_eq h) ≫
            φ.left.stalkMap (genericPoint A.left)).hom.toAlgebra.toModule =
          Nat.card {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1} := by
  sorry
