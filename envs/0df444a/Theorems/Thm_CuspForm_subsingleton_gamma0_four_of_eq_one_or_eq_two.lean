-- Prove2me | Theorems.Thm_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two
-- name    : CuspForm.subsingleton_gamma0_four_of_eq_one_or_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5e46a376-4941-5184-a694-21edc5352ee7
-- title:
--   No weight-4 cusp forms on Γ₀(1) or Γ₀(2)
-- statement:
--   For a natural number $N'$ subject to the hypothesis that $N' = 1$ or $N' = 2$, the type of cusp forms of weight $4$ (the weight being given as the integer $4$) for the congruence subgroup $\Gamma_0(N')$ of $\mathrm{SL}_2(\mathbb{Z})$ is a subsingleton: any two such cusp forms are equal. Since cusp forms of a fixed weight and level form a complex vector space containing $0$, this is equivalent to the assertion that $S_4(\Gamma_0(N')) = 0$ for $N' \in \{1,2\}$. The statement is phrased entirely in Mathlib's language of cusp forms for a congruence subgroup, with $\Gamma_0(N')$ the usual group of integral matrices of determinant $1$ that are upper triangular modulo $N'$; no condition beyond $N' = 1$ or $N' = 2$ is imposed, and the conclusion is the `Subsingleton` property of the type of such forms rather than a dimension formula.
--
--   Classically this is the vanishing of $S_4(\Gamma_0(1))$ and $S_4(\Gamma_0(2))$, the first nonzero cusp forms on these groups occurring in weights $12$ and $8$ respectively. It is used to dispose of the side cases $p = 3$ with small level in the level-lowering step, where a weight-$4$ Hecke algebra acting on a zero space can carry no maximal ideal; it is cited by [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two.lean

import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.subsingleton_gamma0_four_of_eq_one_or_eq_two (N' : ℕ) (hN' : N' = 1 ∨ N' = 2) :
    Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N') (4 : ℤ)) := by sorry
