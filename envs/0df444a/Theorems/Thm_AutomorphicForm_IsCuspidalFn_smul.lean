-- Prove2me | Theorems.Thm_AutomorphicForm_IsCuspidalFn_smul
-- name    : AutomorphicForm.IsCuspidalFn.smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/7aa01d24-2518-598a-a67f-7db1bf5d55c7
-- title:
--   Cuspidality is preserved by scalar multiplication
-- statement:
--   Let $Q$ be a measurable space, $G$ a group, $\mu$ a measure on $Q$, $u : Q \to G$ a map, and $f : G \to \mathbb{C}$ a function. The predicate [`AutomorphicForm.IsCuspidalFn`](def/AutomorphicForm_ConstantTerm.html#L58) $\mu$ $u$ $f$ asserts that for every $g \in G$ the constant term $\mathrm{constantTerm}\ \mu\ u\ f\ g$, defined as the Bochner integral over $Q$ of the integrand $q \mapsto \mathrm{constantTermIntegrand}\ u\ f\ g\ q$ against $\mu$, vanishes. The theorem states: if $f$ satisfies this vanishing condition for all $g$, then for every scalar $c \in \mathbb{C}$ the function $x \mapsto c \cdot f(x)$ satisfies it as well, i.e. all of its constant terms $\mathrm{constantTerm}\ \mu\ u\ (c \cdot f)\ g$ vanish too. No integrability, continuity or invariance hypotheses on $f$, and no hypotheses on $\mu$ or $u$, are imposed.
--
--   This is one of the closure properties making the cuspidal functions, in the sense of vanishing of all constant-term integrals attached to the datum $(\mu, u)$, a complex subspace of the space of functions on $G$. It is used in the Langlands–Tunnell part of the development, in the constructions of a Casimir eigenvector of minimal weight in a continuous realisation and of a nonzero element in an intersection of isotypic cuspidal and weight-cut subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsCuspidalFn_smul.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm MeasureTheory

theorem AutomorphicForm.IsCuspidalFn.smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : AutomorphicForm.IsCuspidalFn μ u f) (c : ℂ) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => c * f x) := by sorry
