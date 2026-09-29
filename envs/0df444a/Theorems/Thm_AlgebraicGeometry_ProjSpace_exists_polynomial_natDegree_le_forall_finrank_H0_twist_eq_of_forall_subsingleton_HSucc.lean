-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
-- name    : AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/abc583d7-111d-5913-90ed-1a3a7da91f95
-- title:
--   Hilbert polynomial for h⁰(mathcal O_Z(d)) above a vanishing threshold
-- statement:
--   Let $k$ be a field, $n$ a natural number, and let $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous components of $k[X_0,\dots,X_n]$ be a closed immersion of schemes. Write $F_d$ for the presheaf of $k$-modules `ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d` on $Z$, whose sections over an open $U$ are the families $(g_i)_{i \in \mathrm{Fin}(n+1)}$ with $g_i \in \Gamma(Z, U \sqcap \mathrm{pullbackChart}\ \iota\ i)$ satisfying the degree-$d$ compatibility condition `TwistCompat`, with restriction maps induced by restriction of sections; and write $K$ for the ordered affine cover `ProjSpace.stdCoverPullback ι` of $Z$ indexed by $\mathrm{Fin}(n+1)$ with $j$-th member $\iota^{-1}(D_+(X_j))$. Assume that for every $d \ge D$ and every $i$ the module $F_d.\mathrm{HSucc}\ K\ i$, that is $\ker d_{i+1} / \operatorname{im} d_i$ in the ordered Čech complex of $F_d$ on $K$, is trivial. Then there is a polynomial $P \in \mathbb{Q}[t]$ with $\deg P \le n$ such that for every $d \ge D$ the $k$-dimension of $F_d.\mathrm{H0}\ K = \ker d_0$, viewed in $\mathbb{Q}$, equals $P(d)$.
--
--   This is the Snapper-type statement that the Hilbert function $d \mapsto h^0(Z, \mathcal O_Z(d))$ of a closed subscheme of $\mathbb{P}^n_k$ is given by a polynomial of degree at most $n$, with the agreement holding from the given threshold $D$ on rather than merely for large $d$. It feeds the construction of the Hilbert functor and the analysis of $H^0$ of twists under maximal growth.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] (D : ℕ)
    (hvan : ∀ d : ℕ, D ≤ d → ∀ i : ℕ,
      Subsingleton ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).HSucc (ProjSpace.stdCoverPullback ι) i)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧
      ∀ d : ℕ, D ≤ d →
        (Module.finrank k ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι)) : ℚ) = P.eval (d : ℚ) := by sorry
