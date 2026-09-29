-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite
-- name    : AlgebraicGeometry.Scheme.exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/bc1e91d2-fee5-5665-bfe0-27dbdef819e1
-- title:
--   Norm of a cocycle of units on the invariant cores of charts
-- statement:
--   Let $X$ be a scheme (in universe $0$), let $\Gamma$ be a finite group acting on $X$ through a group homomorphism $\rho : \Gamma \to \operatorname{Aut} X$, let $r$ be a natural number, let $U : \mathrm{Fin}\,r \to X.\mathrm{Opens}$ be a family of open subschemes, and let $w_{ij} \in \Gamma(X, U_i)$ be sections indexed by pairs $i,j$ satisfying: $w_{ii} = 1$ for all $i$; for all $i,j,k$ the restriction of $w_{ik}$ to $U_i \sqcap U_j$ equals the product of the restriction of $w_{ij}$ (along $U_i \sqcap U_j \le U_i$) with the restriction of $w_{jk}$ (along $U_i \sqcap U_j \le U_j$); and $X.\mathrm{basicOpen}(w_{ij}) = U_i \sqcap U_j$ for all $i,j$. The conclusion asserts the existence of a family of opens $U'_i$, a proof $h$ that $(\rho\gamma).\mathrm{hom}^{-1}(U'_i) = U'_i$ for every $\gamma \in \Gamma$ and every $i$, and sections $w'_{ij} \in \Gamma(X, U'_i)$, such that: $U'_i = \bigsqcap_{\gamma \in \Gamma} (\rho\gamma).\mathrm{hom}^{-1}(U_i)$ for each $i$; $w'_{ii} = 1$; the same cocycle identity holds for the $w'$ on the intersections $U'_i \sqcap U'_j$; $X.\mathrm{basicOpen}(w'_{ij}) = U'_i \sqcap U'_j$; and each $w'_{ij}$ is $\Gamma$-invariant, in the sense that for every $\gamma$ the map $(\rho\gamma).\mathrm{hom}.\mathrm{appLE}$ from $\Gamma(X,U'_i)$ to $\Gamma(X,U'_i)$, formed using the invariance $h$, sends $w'_{ij}$ to $w'_{ij}$.
--
--   This is the norm construction that replaces a family of charts with transition units by its $\Gamma$-invariant core: the opens are shrunk to their $\Gamma$-invariant interiors and the transition units are replaced by their norms along $\Gamma$, preserving the normalisation, cocycle and basic-open properties. It is used by [`AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`](thm.html#AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj), on the way to quasi-projectivity of a quotient of a quasi-projective scheme by a finite group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite
    (X : Scheme.{0}) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X)
    (r : ℕ) (U : Fin r → X.Opens) (w : ∀ i j : Fin r, Γ(X, U i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
        X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
          X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k))
    (hw3 : ∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j) :
    ∃ (U' : Fin r → X.Opens) (hinv : ∀ (γ : Γ) (i : Fin r), (ρ γ).hom ⁻¹ᵁ U' i = U' i)
      (w' : ∀ i j : Fin r, Γ(X, U' i)),
      (∀ i, U' i = ⨅ γ : Γ, (ρ γ).hom ⁻¹ᵁ U i) ∧
      (∀ i, w' i i = 1) ∧
      (∀ i j k : Fin r,
        X.presheaf.map (homOfLE (inf_le_left : U' i ⊓ U' j ≤ U' i)).op (w' i k) =
          X.presheaf.map (homOfLE (inf_le_left : U' i ⊓ U' j ≤ U' i)).op (w' i j) *
            X.presheaf.map (homOfLE (inf_le_right : U' i ⊓ U' j ≤ U' j)).op (w' j k)) ∧
      (∀ i j : Fin r, X.basicOpen (w' i j) = U' i ⊓ U' j) ∧
      (∀ (γ : Γ) (i j : Fin r), (ρ γ).hom.appLE (U' i) (U' i) (le_of_eq (hinv γ i).symm) (w' i j) = w' i j) := by sorry
