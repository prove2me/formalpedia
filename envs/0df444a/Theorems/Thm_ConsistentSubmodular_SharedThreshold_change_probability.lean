-- Prove2me | Theorems.Thm_ConsistentSubmodular_SharedThreshold_change_probability
-- name    : ConsistentSubmodular.SharedThreshold.change_probability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:07.504268+00:00
-- url     : https://prove2.me/theorems/9cf55e2e-89f0-4c29-9eb4-9bacb2ea8182
-- title:
--   Shared-threshold coupling changes membership with probability $|z_s-z_t|$
-- statement:
--   Let $z=(z_t)_{t<d}$ be a vector of probabilities and let $T$ be a shared-threshold coupling for $z$: a finite probability law on cells $\omega$ with active sets $\mathrm{active}(\omega)\subseteq\{0,\dots,d-1\}$ such that $\Pr[t\in\mathrm{active}]=z_t$ for every $t$ and $z_s\le z_t,\ s\in\mathrm{active}(\omega)\Rightarrow t\in\mathrm{active}(\omega)$. Then for all $s,t$,
--   $$\Pr\Bigl[\bigl(s\in\mathrm{active}\wedge t\notin\mathrm{active}\bigr)\ \vee\ \bigl(t\in\mathrm{active}\wedge s\notin\mathrm{active}\bigr)\Bigr]\;=\;|z_s-z_t| .$$
--
--   That is, the probability that exactly one of $s,t$ is active equals the difference of their marginals. This gives the exact expected change of a coordinate between two coupled samples, used to bound recourse by the $\ell_1$ distance of type vectors.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SharedThreshold.lean#L114-L134 (`ConsistentSubmodular.SharedThreshold.change_probability`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.SharedThreshold
variable {d : ℕ} {z : Fin d → ℝ} (T : SharedThreshold z)

theorem ConsistentSubmodular.SharedThreshold.change_probability (s t : Fin d) :
    T.law.probability (fun ω =>
      (s ∈ T.active ω ∧ t ∉ T.active ω) ∨ (t ∈ T.active ω ∧ s ∉ T.active ω)) = |z s - z t| := by sorry
