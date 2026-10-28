-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
-- name    : AlgebraicGeometry.exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T22:39:49.525991+00:00
-- url     : https://prove2.me/theorems/77bad564-392b-4202-9bf6-e267f19ec58c
-- title:
--   Normal projective completion retaining an entire dominating smooth proper family component
-- statement:
--   Let $k$ be a field and let $X,S$ be integral proper projective $k$-schemes with specified projective embeddings. Let $u:U\hookrightarrow S$ be a dense open immersion with $U$ integral. Suppose that $p:Y\to U$ is smooth and proper, that $Y$ is noetherian as a topological space, and that $Y$ is smooth over $k$ through $p,u$ and the structure map of $S$. Assume also that $Y$ has a specified immersion into projective space over $k$, compatible with that structure map, and a dominant $k$-morphism $a:Y\to X$.
--
--   There are a nonempty integral open and closed subscheme $V\subset Y$ and a normal integral projective $k$-scheme $G$ with proper surjections
--   $$q_X:G\to X,\qquad q_S:G\to S.$$
--   The restricted family $V\to U$ is still smooth and proper, and is surjective. The map $V\to X$ remains dominant. A specified dense open immersion $t:V\hookrightarrow G$ satisfies
--   $$q_X\circ t=a|_V,\qquad V\simeq G\times_S U.$$
--   The second assertion is an actual cartesian square with the original maps $t,V\to U,q_S,u$, so the whole proper family component is recovered over $U$. Its total space is smooth over $k$. Both maps from $G$ have the same $k$-structure, and
--   $$\dim G=\dim V.$$
--   A closed embedding of this same $G$ into projective space over $k$, with the required structure-map equation, is retained.
--
--   The theorem holds in arbitrary universes and characteristic. It supplies a global normal projective model whose restriction over the dense base open is the actual smooth proper covering-family component. The theorem asserts smoothness on that retained open; smoothness of the entire completion, semistable extension over the base boundary and a global smooth alteration are further steps.
-- source:
--   Auxiliary projective family-completion theorem for the Philippon curve-fibration alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . It extends the accepted covering-family construction https://prove2.me/theorems/ae594a3b-8d61-41b8-8e72-b6a40e8b9e2f by selecting an open and closed integral component, taking the graph of both original maps, and normalizing while retaining the specified normal open. The component selection and exact proper-family retention are proved using Mathlib; projective products, scheme-theoretic images, finite normalization and its projectivity reuse Proved platform inputs. It is a normal projective completion, not the final smooth alteration.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
    (k : Type u) [Field k] {Y X S U : Scheme.{u}}
    [NoetherianSpace Y] [IsIntegral X] [IsIntegral S] [IsIntegral U]
    (u : U ⟶ S) [IsOpenImmersion u] [IsDominant u]
    (p : Y ⟶ U) [Smooth p] [IsProper p]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    [Smooth (p ≫ u ≫ πS)]
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsImmersion j] (hj : j ≫ ProjSpace.π k n = p ≫ u ≫ πS)
    (a : Y ⟶ X) [IsDominant a] (ha : a ≫ πX = p ≫ u ≫ πS) :
    ∃ (V : Y.Opens) (G : Scheme.{u}) (qX : G ⟶ X) (qS : G ⟶ S)
      (t : (V : Scheme.{u}) ⟶ G),
      IsIntegral V ∧ IsClosedImmersion V.ι ∧
      Smooth (V.ι ≫ p) ∧ IsProper (V.ι ≫ p) ∧ Surjective (V.ι ≫ p) ∧
      Smooth (V.ι ≫ p ≫ u ≫ πS) ∧ IsDominant (V.ι ≫ a) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper qX ∧ Surjective qX ∧ IsProper qS ∧ Surjective qS ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ qX = V.ι ≫ a ∧
      IsPullback t (V.ι ≫ p) qS u ∧ qX ≫ πX = qS ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim V ∧
      ∃ (d : ℕ) (l : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion l ∧ l ≫ ProjSpace.π k d = qX ≫ πX := by sorry
