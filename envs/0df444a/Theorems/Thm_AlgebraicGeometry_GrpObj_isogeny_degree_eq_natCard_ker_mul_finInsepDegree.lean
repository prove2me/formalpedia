-- Prove2me | Theorems.Thm_AlgebraicGeometry_GrpObj_isogeny_degree_eq_natCard_ker_mul_finInsepDegree
-- name    : AlgebraicGeometry.GrpObj.isogeny_degree_eq_natCard_ker_mul_finInsepDegree
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:54:09.951225+00:00
-- url     : https://prove2.me/theorems/b77192a4-c11c-4794-b43a-429f980869ca
-- title:
--   Degree of an isogeny of a proper integral group variety: the kernel count is the separable degree, and the degree is that count times a power of the characteristic
-- statement:
--   Let $k$ be an algebraically closed field and let $A$ be a group scheme over $k$ whose structure morphism $A \to \operatorname{Spec} k$ is proper and whose underlying scheme is integral (for example an abelian variety). Write $K(A)$ for the function field of $A$, $\eta$ for its generic point, and, for an endomorphism of group schemes $\varphi \colon A \to A$ over $k$, write $\ker\varphi(k)$ for the set of $k$-points $c$ of $A$ with $\varphi(c) = e$.
--
--   If an endomorphism $\psi$ of $A$ over $k$ satisfies $\psi(\eta) = \eta$ (equivalently, $\psi$ is dominant), it induces a field homomorphism $\psi^* \colon K(A) \to K(A)$, the pull-back of rational functions, through which $K(A)$ is an extension of $\psi^* K(A)$. The *degree* of $\psi$ is $\deg\psi = [K(A) : \psi^* K(A)]$ if $\psi(\eta) = \eta$, and $\deg\psi = 0$ otherwise. Then, for every endomorphism of group schemes $\varphi$ of $A$:
--
--   1. $\varphi$ is dominant if and only if $\ker\varphi(k)$ is finite;
--   2. $\deg\varphi = 0$ if and only if $\varphi$ is not dominant;
--   3. $\deg(\varphi \circ \psi) = \deg\varphi \cdot \deg\psi$ for every endomorphism of group schemes $\psi$ of $A$;
--   4. if $\varphi$ is dominant (an isogeny), then $\varphi$ is a finite and surjective morphism, $\#\ker\varphi(k) = [K(A) : \varphi^* K(A)]_s$ is the separable degree of the extension, every fibre $\varphi^{-1}(y)$ over a closed point $y$ of $A$ has exactly $\#\ker\varphi(k)$ points, and $\deg\varphi = [K(A) : \varphi^* K(A)]_s \cdot [K(A) : \varphi^* K(A)]_i$, where the inseparable degree $[K(A) : \varphi^* K(A)]_i$ is a power of the exponential characteristic of $k$.
--
--   In particular $\deg\varphi = \#\ker\varphi(k) \cdot p^e$ for some $e \ge 0$ when $k$ has characteristic $p > 0$, and $\deg\varphi = \#\ker\varphi(k)$ in characteristic $0$. For example, the identity has degree $1$ and trivial kernel, and when $\dim A > 0$ the constant endomorphism $e$ is not dominant, has degree $0$ and kernel $A(k)$, which is infinite.
--
--   **Formalization Note**: A group scheme over $k$ is `A : Over (Spec (.of k))` with `GrpObj A` for the cartesian monoidal structure of `Over (Spec k)` (the product is the fibre product over $k$); `A.left` is the scheme and `A.hom` its structure morphism. Endomorphisms over $k$ are morphisms `A ⟶ A` in `Over (Spec k)`, and endomorphisms of group schemes are those with `IsMonHom`; `ψ ≫ φ` is $\varphi \circ \psi$. The pull-back $\psi^*$ and the degree are given as variables with defining hypotheses: `hff` says that for every `ψ` with `ψ.left (genericPoint A.left) = genericPoint A.left`, `ff ψ` is the stalk map of `ψ.left` at the generic point, preceded by the identification `stalkSpecializes` of the stalk at $\eta$ with the stalk at $\psi(\eta) = \eta$ (the function field `A.left.functionField` is the stalk at the generic point); `ff ψ` is unconstrained for other `ψ` and is only used for dominant `φ`. `hdeg` and `hdeg0` define `deg ψ` as above, so `deg` is uniquely determined. Because `A.left.functionField` is also an algebra over itself through the identity, the algebra structure given by `ff ψ` is passed explicitly: `@Module.finrank _ _ _ _ (ff ψ).toAlgebra.toModule` is $[K(A) : \psi^* K(A)]$, and `@Field.finSepDegree _ _ _ _ (ff φ).toAlgebra`, `@Field.finInsepDegree _ _ _ _ (ff φ).toAlgebra` are the separable and inseparable degrees of that extension (Mathlib's `Field.finSepDegree`, `Field.finInsepDegree`); `ringExpChar k` is the exponential characteristic. The $k$-points of $A$ are the sections `c : 𝟙_ (Over (Spec (.of k))) ⟶ A` (morphisms from `Spec k` over `Spec k`); they form a group through `GrpObj A`, whose unit `1` is the identity section, so the kernel is the subtype `{c // c ≫ φ = 1}`. A closed point is a `y : A.left` with `IsClosed {y}`, and `φ.left ⁻¹' {y}` is the set of points of the fibre.
-- source:
--   J. S. Milne, Abelian Varieties (version 2.00, 2008), Part I, Section 7 (Isogenies), Proposition 7.1; D. Mumford, Abelian Varieties, Tata Institute of Fundamental Research Studies in Mathematics 5 (1970), Section 4

import Mathlib

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

theorem AlgebraicGeometry.GrpObj.isogeny_degree_eq_natCard_ker_mul_finInsepDegree
    (k : Type) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [IsIntegral A.left]
    (ff : (A ⟶ A) → (A.left.functionField →+* A.left.functionField))
    (hff : ∀ (ψ : A ⟶ A) (h : ψ.left (genericPoint A.left) = genericPoint A.left),
      ff ψ = (A.left.presheaf.stalkSpecializes (specializes_of_eq h) ≫
        ψ.left.stalkMap (genericPoint A.left)).hom)
    (deg : (A ⟶ A) → ℕ)
    (hdeg : ∀ ψ : A ⟶ A, ψ.left (genericPoint A.left) = genericPoint A.left →
      deg ψ = @Module.finrank _ _ _ _ (ff ψ).toAlgebra.toModule)
    (hdeg0 : ∀ ψ : A ⟶ A, ψ.left (genericPoint A.left) ≠ genericPoint A.left → deg ψ = 0)
    (φ : A ⟶ A) [IsMonHom φ] :
    (IsDominant φ.left ↔ Finite {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1}) ∧
    (deg φ = 0 ↔ ¬ IsDominant φ.left) ∧
    (∀ (ψ : A ⟶ A) [IsMonHom ψ], deg (ψ ≫ φ) = deg φ * deg ψ) ∧
    (IsDominant φ.left →
      IsFinite φ.left ∧ Function.Surjective φ.left ∧
      Nat.card {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1} =
        @Field.finSepDegree _ _ _ _ (ff φ).toAlgebra ∧
      (∀ y : A.left, IsClosed ({y} : Set A.left) →
        Nat.card (φ.left ⁻¹' {y}) = Nat.card {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1}) ∧
      deg φ = @Field.finSepDegree _ _ _ _ (ff φ).toAlgebra *
        @Field.finInsepDegree _ _ _ _ (ff φ).toAlgebra ∧
      ∃ n : ℕ, @Field.finInsepDegree _ _ _ _ (ff φ).toAlgebra = ringExpChar k ^ n) := by
  sorry
