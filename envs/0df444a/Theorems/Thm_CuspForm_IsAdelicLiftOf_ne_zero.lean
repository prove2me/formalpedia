-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_ne_zero
-- name    : CuspForm.IsAdelicLiftOf.ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/dca76292-bdba-59b1-93dc-32bb900739bf
-- title:
--   Nonvanishing of an adelic lift of a cusp form
-- statement:
--   Let $M$ be a natural number, let $g$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(M)$, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ (the units of the $2\times 2$ matrices over `AdeleRing (RingOfIntegers ℚ) ℚ`). Assume `g.IsAdelicLiftOf φ`, that is: (i) $\varphi(\iota(\gamma)x)=\varphi(x)$ for every $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and every adelic $x$, where $\iota$ is the map [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) induced by $\mathbb{Q}\to\mathbb{A}_\mathbb{Q}$; (ii) $\varphi(x\cdot \mathrm{finEmbed}(u))=\varphi(x)$ for all $x$ and all $u$ in the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) attached to the ideal $\mathrm{span}\{M\}$ of $\mathcal{O}_\mathbb{Q}$, consisting of those $u\in\mathrm{GL}_2$ of the finite adeles for which both the matrix of $u$ and that of $u^{-1}$ satisfy the predicate `IsLevelOneMatrix` at that ideal, embedded into the full adelic group by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145); and (iii) for every adelic $h$ whose finite part `glFin h` is trivial and whose archimedean image [`LanglandsTunnell.ratArchGL2 h`](def/LanglandsTunnell_DeltaLift.html#L16) lies in $\mathrm{GL}_2^+(\mathbb{R})$, one has $\varphi(h)=\bigl(g\mid_{2}\mathrm{ratArchGL2}(h)\bigr)(i)$, the weight-$2$ slash action evaluated at $i\in\mathbb{H}$. Then $g\neq 0$ implies $\varphi\neq 0$.
--
--   The statement records that the adelic lift of a classical weight-two cusp form detects nonvanishing: a lift of a nonzero form is itself a nonzero function on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$. It is used where the adelic automorphic form attached to a newform must be known to be nonzero, for instance when identifying the span it generates or when passing from a newform to the associated Galois representation and its local behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_ne_zero.lean

import Definitions.Def_CuspForm_AdelicLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.ne_zero
    {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : g.IsAdelicLiftOf φ)
    (hg : g ≠ 0) : φ ≠ 0 := by sorry
