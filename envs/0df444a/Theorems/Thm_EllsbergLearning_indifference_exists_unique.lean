-- Prove2me | Theorems.Thm_EllsbergLearning_indifference_exists_unique
-- name    : EllsbergLearning.indifference_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:59.288847+00:00
-- url     : https://prove2.me/theorems/5448279c-298b-413a-b2d4-a2d2c78bd6f3
-- title:
--   §4, p.19 — the indifference point $(\underline\pi,\overline\pi,\tilde z)$ exists and is unique
-- statement:
--   Under the standing assumptions there is exactly one pair of probabilities $\underline\pi,\overline\pi$ and one deterministic signal trajectory $(\tilde z_t)$ such that for every $t$
--   $$\underline\pi=\underline m_t(\tilde z_t),\qquad \overline\pi=\overline m_t(\tilde z_t),\qquad \underline\pi u_{11}+(1-\underline\pi)u_{10}=\overline\pi u_{01}+(1-\overline\pi)u_{00}.$$
--   At the signal $\tilde z_t$ the decision maker is indifferent between $a_0$ and $a_1$; $a_0$ ($a_1$) is preferred below (above) it. The trajectory separates the two regimes of the worst-case prior.
--
--   Differences from the source:
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: a trajectory $(\tilde z_t)_{t\ge0}$ → a function $\tilde z:\mathbb R\to\mathbb R$ with the defining identities for every real $t$; reason: the closed forms extend to all real $t$; the paper's trajectory is the restriction to $t\ge0$, and uniqueness on $\mathbb R$ implies uniqueness on $[0,\infty)$
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §4, p.19

import Definitions.Def_EllsbergLearning_Params

namespace EllsbergLearning

/-- The indifference point (Epstein & Ji, arXiv:1708.01890v2, §4, p.19): under the standing
assumptions of §3.1 there is exactly one triple `(π̲, π̄, z̃)` of two numbers and a signal
trajectory such that, for every `t`, `π̲ = m̲_t(z̃_t)`, `π̄ = m̄_t(z̃_t)`, and
`π̲u₁₁ + (1 − π̲)u₁₀ = π̄u₀₁ + (1 − π̄)u₀₀`.

**Formalization Note.** The trajectory is indexed by real `t`; see `Params.IsIndifference`. -/
theorem indifference_exists_unique (p : Params) (hp : p.Valid) :
    ∃! q : ℝ × ℝ × (ℝ → ℝ), p.IsIndifference q.1 q.2.1 q.2.2 := by sorry

end EllsbergLearning
