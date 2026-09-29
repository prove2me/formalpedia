-- Prove2me | Theorems.Thm_AutomorphicForm_IsCuspidalFn_rightTranslate
-- name    : AutomorphicForm.IsCuspidalFn.rightTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/d4856455-ffe2-53d1-b641-b951806cd0df
-- title:
--   Cuspidality is preserved by right translation
-- statement:
--   Let $Q$ be a measurable space carrying a measure $\mu$, let $G$ be a group, let $u : Q \to G$ be a map, and let $f : G \to \mathbb{C}$. Call $f$ cuspidal, in the sense of the predicate [`AutomorphicForm.IsCuspidalFn`](def/AutomorphicForm_ConstantTerm.html#L58), when for every $g \in G$ the constant term $\int_Q (\mathtt{constantTermIntegrand}\ u\ f\ g)(q)\, d\mu(q)$ vanishes, where [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) is by definition this Bochner integral over $Q$ of the integrand [`AutomorphicForm.constantTermIntegrand u f g`](def/AutomorphicForm_ConstantTerm.html#L44) built from $u$, $f$ and the point $g$. The theorem asserts: if $f$ is cuspidal in this sense and $h \in G$ is arbitrary, then the right translate $x \mapsto f(xh)$ is again cuspidal, i.e. its constant term at every $g \in G$ is zero. No integrability, measurability or continuity hypotheses on $f$ or $u$ are imposed beyond the measurable space structure on $Q$ and the group structure on $G$; the statement holds with the convention that a non-integrable Bochner integral is zero.
--
--   This is the invariance of the cuspidal condition under the right regular representation of $G$: the space of cuspidal functions is stable under right translation. It is used to show that right translates of cuspidal members stay in the cuspidal submodule, in [`AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule`](thm.html#AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsCuspidalFn_rightTranslate.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm MeasureTheory

theorem AutomorphicForm.IsCuspidalFn.rightTranslate
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : AutomorphicForm.IsCuspidalFn μ u f) (h : G) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => f (x * h)) := by sorry
