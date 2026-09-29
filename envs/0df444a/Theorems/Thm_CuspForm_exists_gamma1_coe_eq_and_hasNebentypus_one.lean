-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one
-- name    : CuspForm.exists_gamma1_coe_eq_and_hasNebentypus_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/53a8d1bc-cd4b-5b0e-96c2-ad6c6834a8c7
-- title:
--   A Γ₀(M) cusp form as a Γ₁(M) form with trivial nebentypus
-- statement:
--   Let $M$ be a natural number, $k$ an integer, and let $g$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(M)$ in the sense of Mathlib's `CuspForm`. The assertion is that there exists a cusp form $g_1$ of weight $k$ for $\Gamma_1(M)$ such that, first, the underlying functions on the upper half-plane agree, $\mathord{\Uparrow} g_1 = \mathord{\Uparrow} g$ as maps $\mathbb{H} \to \mathbb{C}$, and second, $g_1$ satisfies [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) for the trivial Dirichlet character $1 \in$ `DirichletCharacter ℂ M`; unfolding that predicate, for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane,
--   $$g_1(\gamma \cdot \tau) = \varepsilon\big(\gamma_{1,1} \bmod M\big)\cdot\Big(\big(\gamma_{1,0}\,\tau + \gamma_{1,1}\big)^{k}\, g_1(\tau)\Big)$$
--   with $\varepsilon = 1$ the trivial character, the entries $\gamma_{1,0}, \gamma_{1,1}$ of the lower row being cast into $\mathbb{Z}/M$ respectively into $\mathbb{C}$. No positivity or nonvanishing hypothesis is imposed on $M$, and $k$ is an arbitrary integer.
--
--   This is the standard identification $S_k(M,\mathbf 1) = S_k(\Gamma_0(M))$ inside the decomposition $S_k(\Gamma_1(M)) = \bigoplus_{\varepsilon} S_k(M,\varepsilon)$ by nebentypus, realised here as restriction of the invariance condition along $\Gamma_1(M) \le \Gamma_0(M)$. It is used to feed $\Gamma_0(M)$ cusp forms into results stated for $\Gamma_1(M)$ forms with a nebentypus character, in the adelic lifting and isotypic-component statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.exists_gamma1_coe_eq_and_hasNebentypus_one
    {M : ℕ} (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g₁ : CuspForm (CongruenceSubgroup.Gamma1 M) k,
      (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g ∧ CuspForm.HasNebentypus (1 : DirichletCharacter ℂ M) g₁ := by sorry
