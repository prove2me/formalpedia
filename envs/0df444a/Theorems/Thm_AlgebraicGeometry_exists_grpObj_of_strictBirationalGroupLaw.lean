-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_grpObj_of_strictBirationalGroupLaw
-- name    : AlgebraicGeometry.exists_grpObj_of_strictBirationalGroupLaw
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-24T23:14:25.050844+00:00
-- url     : https://prove2.me/theorems/204dcb51-85dc-45c3-8157-d30bd926bfba
-- title:
--   Weil's group chunk theorem: a strict birational group law on an integral scheme over an algebraically closed field comes from a group scheme, unique up to unique isomorphism
-- statement:
--   Let $k$ be an algebraically closed field and let $X$ be an integral scheme with a morphism $s_X \colon X \to \operatorname{Spec} k$ that is separated, locally of finite type and geometrically reduced (over an algebraically closed field, geometrically reduced is the same as reduced). A *strict birational group law* on $X$ consists of an open subscheme $\Omega \subseteq X \times_k X$ and a morphism $m \colon \Omega \to X$, written $(x, y) \mapsto xy$, such that:
--
--   1. the two morphisms $\Phi, \Psi \colon \Omega \to X \times_k X$, $\Phi(x, y) = (x, xy)$ and $\Psi(x, y) = (xy, y)$, are open immersions;
--   2. every closed point $a$ of $X$ is the first coordinate of some closed point of $\Omega$, and every closed point $b$ of $X$ is the second coordinate of some closed point of $\Omega$;
--   3. $m$ is associative on closed points: $(ab)c = a(bc)$ whenever $(a, b)$, $(b, c)$, $(ab, c)$ and $(a, bc)$ are closed points of $\Omega$.
--
--   Then there is a group scheme $G$ over $k$ that is smooth, separated, locally of finite type and integral, together with an open immersion $j \colon X \to G$ over $k$ with dense image, such that $j$ carries $m$ to the multiplication of $G$: $j(xy) = j(x)\,j(y)$ on $\Omega$, that is, $j \times_k j$ restricted to $\Omega$ and followed by the multiplication $G \times_k G \to G$ equals $m$ followed by $j$.
--
--   Moreover $(G, j)$ is unique up to unique isomorphism: if $G'$ is any group scheme over $k$ that is locally of finite type, separated and integral, and $j' \colon X \to G'$ is an open immersion over $k$ with $j'(xy) = j'(x)\,j'(y)$ on $\Omega$ in the same sense, then there is exactly one isomorphism of schemes $e \colon G \to G'$ over $k$ with $e \circ j = j'$.
--
--   For example, a smooth connected group variety $X$ with $\Omega = X \times_k X$ and $m$ its multiplication satisfies the hypotheses; the theorem is used for laws that are defined only on a dense open $\Omega$, such as the law $(D, E) \mapsto$ the unique effective divisor linearly equivalent to $D + E - g\,P_0$ on a dense open of the symmetric power $C^{(g)}$ of a curve of genus $g$.
--
--   Role: this is Weil's construction of an algebraic group from a group chunk (a birational group law), the step that turns the birational group law on $C^{(g)}$ into the Jacobian of $C$, and the field case of the construction of group schemes from birational group laws used for Néron models.
--
--   **Formalization Note**: $X \times_k X$ is `pullback sX sX`, $\Omega$ is `Ω : (pullback sX sX).Opens` and $m$ is a morphism from the open subscheme `Ω.toScheme`. The morphisms $\Phi$ and $\Psi$ are given as variables `Φ`, `Ψ` with their defining hypotheses: `hΦ₁`, `hΦ₂` say that the two projections of $\Phi$ are $(x, y) \mapsto x$ and $m$, and `hΨ₁`, `hΨ₂` that those of $\Psi$ are $m$ and $(x, y) \mapsto y$; by the universal property of the fibre product this determines them. A closed point is a point `a` with `IsClosed {a}`; the closed points of $\Omega$ are the `z : Ω` with `IsClosed {z.1}` in $X \times_k X$. In `hassoc`, $z_1 = (a, b)$, $z_2 = (b, c)$, $z_3 = (ab, c)$ and $z_4 = (a, bc)$. A group scheme over $k$ is `G : Over (Spec k)` with `GrpObj G` for the cartesian monoidal structure of `Over (Spec k)` (the product is the fibre product over $k$); `G.left` is the scheme and `G.hom` its structure morphism. `(G ⊗ G).left` is `pullback G.hom G.hom`, so `pullback.map sX sX G.hom G.hom j j (𝟙 _) _ _` is $j \times_k j$ and `(MonObj.mul : G ⊗ G ⟶ G).left` is the multiplication. The uniqueness clause assumes no smoothness of $G'$, and $e$ is asserted to be an isomorphism of $k$-schemes compatible with $j$ and $j'$ (it is then automatically compatible with the group laws, but that is not part of the statement). $G$ is asserted to be locally of finite type; that it is of finite type is not part of the statement.
-- source:
--   A. Weil, On algebraic groups of transformations, Amer. J. Math. 77 (1955), 355-391; S. Bosch, W. Lütkebohmert, M. Raynaud, Néron Models, Springer 1990, Chapter 5

import Mathlib

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.exists_grpObj_of_strictBirationalGroupLaw
    (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsSeparated sX] [LocallyOfFiniteType sX] [GeometricallyReduced sX]
    (Ω : (pullback sX sX).Opens) (m : Ω.toScheme ⟶ X)
    (Φ : Ω.toScheme ⟶ pullback sX sX) (hΦ₁ : Φ ≫ pullback.fst sX sX = Ω.ι ≫ pullback.fst sX sX)
    (hΦ₂ : Φ ≫ pullback.snd sX sX = m) (hΦ : IsOpenImmersion Φ)
    (Ψ : Ω.toScheme ⟶ pullback sX sX) (hΨ₁ : Ψ ≫ pullback.fst sX sX = m)
    (hΨ₂ : Ψ ≫ pullback.snd sX sX = Ω.ι ≫ pullback.snd sX sX) (hΨ : IsOpenImmersion Ψ)
    (hleft : ∀ a : X, IsClosed ({a} : Set X) →
      ∃ z ∈ Ω, IsClosed ({z} : Set (pullback sX sX : Scheme.{0})) ∧ pullback.fst sX sX z = a)
    (hright : ∀ b : X, IsClosed ({b} : Set X) →
      ∃ z ∈ Ω, IsClosed ({z} : Set (pullback sX sX : Scheme.{0})) ∧ pullback.snd sX sX z = b)
    (hassoc : ∀ z₁ z₂ z₃ z₄ : Ω, IsClosed {z₁.1} → IsClosed {z₂.1} → IsClosed {z₃.1} → IsClosed {z₄.1} →
      pullback.snd sX sX z₁.1 = pullback.fst sX sX z₂.1 →
      pullback.fst sX sX z₃.1 = m z₁ → pullback.snd sX sX z₃.1 = pullback.snd sX sX z₂.1 →
      pullback.fst sX sX z₄.1 = pullback.fst sX sX z₁.1 → pullback.snd sX sX z₄.1 = m z₂ →
      m z₃ = m z₄) :
    ∃ (G : Over (Spec (.of k))) (_ : GrpObj G) (j : X ⟶ G.left) (hj : j ≫ G.hom = sX),
      Smooth G.hom ∧ IsSeparated G.hom ∧ LocallyOfFiniteType G.hom ∧ IsIntegral G.left ∧
      IsOpenImmersion j ∧ DenseRange j ∧
      Ω.ι ≫ pullback.map sX sX G.hom G.hom j j (𝟙 _) (by rw [hj, Category.comp_id])
          (by rw [hj, Category.comp_id]) ≫ (MonObj.mul : G ⊗ G ⟶ G).left = m ≫ j ∧
      ∀ (G' : Over (Spec (.of k))) [GrpObj G'] [LocallyOfFiniteType G'.hom] [IsSeparated G'.hom]
        [IsIntegral G'.left] (j' : X ⟶ G'.left) (hj' : j' ≫ G'.hom = sX), IsOpenImmersion j' →
        Ω.ι ≫ pullback.map sX sX G'.hom G'.hom j' j' (𝟙 _) (by rw [hj', Category.comp_id])
            (by rw [hj', Category.comp_id]) ≫ (MonObj.mul : G' ⊗ G' ⟶ G').left = m ≫ j' →
        ∃! e : G.left ≅ G'.left, e.hom ≫ G'.hom = G.hom ∧ j ≫ e.hom = j' := by
  sorry
