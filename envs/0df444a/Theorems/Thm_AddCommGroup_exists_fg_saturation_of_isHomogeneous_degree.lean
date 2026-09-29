-- Prove2me | Theorems.Thm_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree
-- name    : AddCommGroup.exists_fg_saturation_of_isHomogeneous_degree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/8d6d1fa4-60b9-580d-aa5e-155096b9aedb
-- title:
--   Finitely generated saturations from a separating homogeneous degree
-- statement:
--   Let $R$ be an additive abelian group and let $\deg \colon R \to \mathbb{Z}$ be an arbitrary function on it. Fix a natural number $D \neq 0$ and assume: (i) for every $m \in \mathbb{N}$ and every family $\alpha \colon \{1,\dots,m\} \to R$ there is a polynomial $P \in \mathbb{Q}[X_1,\dots,X_m]$, homogeneous of degree $D$, such that for all integer vectors $n \in \mathbb{Z}^m$ the rational number $\deg\bigl(\sum_i n_i \cdot \alpha_i\bigr)$ equals the value of $P$ at $(n_1,\dots,n_m)$, the $n_i$ being viewed in $\mathbb{Q}$; and (ii) $\deg x \neq 0$ for every $x \neq 0$ in $R$. Let $M$ be a finitely generated subgroup of $R$. Then there exists a finitely generated subgroup $M'$ of $R$ such that, for every $x \in R$, one has $x \in M'$ if and only if $k \cdot x \in M$ for some non-zero integer $k$. In other words, the saturation of $M$ in $R$, as a set of elements, coincides with a finitely generated subgroup; taking $k = 1$ shows in particular $M \subseteq M'$.
--
--   This is the purely group-theoretic step underlying the finite generation of the endomorphism group of an abelian variety, where $R = \operatorname{End}(A)$, $\deg$ is the degree of an endomorphism and $D = 2g$, hypothesis (ii) reflecting that a non-zero endomorphism of a simple abelian variety is an isogeny. It is used in the construction of relative group laws under good reduction, namely in [`GoodReductionJacobian.RelativeGroupLaw.exists_existsUnique_eq_prod_zpow_of_forall_comm_of_forall_endDegree_ne_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_existsUnique_eq_prod_zpow_of_forall_comm_of_forall_endDegree_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.exists_fg_saturation_of_isHomogeneous_degree
    {R : Type*} [AddCommGroup R] (deg : R → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
      ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
    (hsep : ∀ x : R, x ≠ 0 → deg x ≠ 0)
    (M : AddSubgroup R) (hM : M.FG) :
    ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M := by sorry
