-- Prove2me | Theorems.Thm_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
-- name    : AddCommGroup.moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/49a07363-1812-5467-9433-8c2fabbdb6b5
-- title:
--   Finite freeness from finitely generated saturations and an n-divisible kernel
-- statement:
--   Let $R$ be an additive abelian group that is torsion-free (the `IsAddTorsionFree` assumption), and suppose: (i) for every finitely generated subgroup $M \subseteq R$ there is a finitely generated subgroup $M' \subseteq R$ whose elements are exactly the $x \in R$ for which $kx \in M$ for some integer $k \neq 0$ — that is, the saturation of every finitely generated subgroup is again finitely generated; and (ii) there are a finite additive abelian group $G$, an additive group homomorphism $\rho \colon R \to G$, and a natural number $n$ with $1 < n$ such that every $x \in R$ with $\rho(x) = 0$ can be written as $x = n y$ for some $y \in R$. The conclusion is the conjunction that $R$, viewed as a $\mathbb{Z}$-module, is module-finite over $\mathbb{Z}$ and is a free $\mathbb{Z}$-module; equivalently, $R$ is a finitely generated free abelian group.
--
--   This is the algebraic assembly step in the classical proof that the endomorphism group of an abelian variety is a finitely generated free abelian group: hypothesis (i) comes from a discreteness argument for the degree form, and hypothesis (ii) from the faithful action on the $\ell$-torsion. It is used in the construction of the relative group law in the good-reduction Jacobian development, in [`GoodReductionJacobian.RelativeGroupLaw.exists_existsUnique_eq_prod_zpow_of_forall_comm_of_forall_endDegree_ne_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_existsUnique_eq_prod_zpow_of_forall_comm_of_forall_endDegree_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
    {R : Type*} [AddCommGroup R] [IsAddTorsionFree R]
    (hsat : ∀ M : AddSubgroup R, M.FG →
      ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
    {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ) (hn : 1 < n)
    (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
    Module.Finite ℤ R ∧ Module.Free ℤ R := by sorry
