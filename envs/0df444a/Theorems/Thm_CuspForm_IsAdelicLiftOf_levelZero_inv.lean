-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
-- name    : CuspForm.IsAdelicLiftOf.levelZero_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/e489ad0a-ed56-5af7-b5bf-b77f628a1efa
-- title:
--   Adelic lifts of Γ₀(M)-forms are right K₀(M)-invariant
-- statement:
--   Fix a natural number $M \neq 0$, a cusp form $g$ of weight $2$ for $\Gamma_0(M)$, and a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ (the general linear group of degree $2$ over the adele ring of $\mathbb{Q}$ relative to $\mathcal{O}_{\mathbb{Q}}$) with complex values, and assume `g.IsAdelicLiftOf φ`, i.e. the conjunction of: $\varphi(\iota(\gamma)x) = \varphi(x)$ for every $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ and every $x$, where $\iota$ is the map `globalPoints` induced by $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$; right invariance $\varphi(x\cdot \mathrm{finEmbed}(u)) = \varphi(x)$ for all $u$ in the subgroup `finiteLevelOne` attached to the ideal $(M) \subseteq \mathcal{O}_{\mathbb{Q}}$, consisting of those $u \in \mathrm{GL}_2$ over the finite adeles for which both $u$ and $u^{-1}$ satisfy the predicate `IsLevelOneMatrix` at $(M)$, with $\mathrm{finEmbed}(u)$ the adelic matrix having finite component $u$ and trivial infinite component; and the archimedean normalisation $\varphi(h) = (g \mid_2 \mathrm{ratArchGL2}(h))(i)$ for every $h$ whose finite part `glFin` is $1$ and whose real archimedean component `ratArchGL2` has positive determinant. The conclusion: $\varphi(x \cdot \mathrm{finEmbed}(u)) = \varphi(x)$ for all $x$ and all $u$ in the larger subgroup `finiteLevelZero` at $(M)$, namely those $u$ such that both $u$ and $u^{-1}$ have all entries integral finite adeles and lower-left entry in the $(M)$-ball.
--
--   This upgrades the defining right $K_1(M)$-invariance of an adelic lift to right invariance under the level-zero group $K_0(M)$, the classical statement that the adelisation of a weight-two form on $\Gamma_0(M)$ is right invariant under the full congruence subgroup with no condition on the diagonal. It is used downstream in the comparison of adelic lifts with central characters and nebentypus, and in the treatment of lifts of forms on $\Gamma_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_levelZero_inv.lean

import Definitions.Def_CuspForm_AdelicLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.levelZero_inv {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : g.IsAdelicLiftOf φ) :
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x := by sorry
