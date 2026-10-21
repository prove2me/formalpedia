-- Prove2me | Theorems.Thm_CtxInvOpt_Offline_lemma1_realized_worst_case_regret
-- name    : CtxInvOpt.Offline.lemma1_realized_worst_case_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:49.467203+00:00
-- url     : https://prove2.me/theorems/c5a33ae7-70a1-40cb-a74d-facfd145cb4d
-- title:
--   Lemma 1, p. 11 — the worst-case regret of proxy cost c^π against c⋆ is sin θ(c⋆, c^π), or 1 when θ ≥ π/2
-- statement:
--   Let $n\ge1$ and $d\ge2$. Fix a proxy cost $c^\pi\in S^d$ and a true cost $c^\star\in S^d$. Consider all instances consisting of an action set $\mathcal X\in\mathcal B$ (nonempty, compact, diameter at most $1$), a $1$-Lipschitz context function $f:\mathbb R^n\to\mathbb R^d$, an action $x^\pi\in\psi(c^\pi,\mathcal X,f)$ chosen by the proxy policy (any minimizer, so ties are broken adversarially), and an optimal action $x^\star\in\psi(c^\star,\mathcal X,f)$. The worst-case regret
--   $$\mathcal L(c^\pi,c^\star)=\sup_{x^\pi\in\psi(c^\pi,\mathcal X,f),\ \mathcal X\in\mathcal B,\ f\in\mathcal F}\big(f(x^\pi)-f(x^\star)\big)'c^\star$$
--   is attained and equals
--   $$\mathcal L(c^\pi,c^\star)=\begin{cases}\sin\theta(c^\star,c^\pi)&\text{if }\theta(c^\star,c^\pi)<\pi/2,\\ 1&\text{otherwise.}\end{cases}$$
--
--   The lemma converts a policy that acts as if the cost were $c^\pi$ into a purely geometric quantity: its worst-case loss depends only on the angle between $c^\pi$ and the true cost. It is the basis of the upper bound in Theorem 1.
--
--   **Formalization Note** The supremum is stated with `IsGreatest`: the value is a regret of some admissible instance, and it bounds the regret of every admissible instance. The proxy policy is represented by its cost vector $c^\pi$ (as on p. 10 of the paper). The hypothesis $n\ge1$ is not written in the paper but is needed: in $\mathbb R^0$ every regret is $0$. The hypothesis $d\ge2$ is the paper's standing assumption of §2.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 11, Lemma 1 (with (8), p. 10); proof App-3–App-5

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Offline

/-- **Lemma 1 (Realized worst-case regret), arXiv:2106.14015v3, p. 11.** For a proxy cost
`c^π ∈ S^d` and a true cost `c⋆ ∈ S^d`, the worst-case regret (8)
`L(c^π, c⋆) = sup_{x^π ∈ ψ(c^π, X, f), X ∈ 𝔅, f ∈ 𝔉} (f(x^π) − f(x⋆))′c⋆`
equals `sin θ(c⋆, c^π)` if `θ(c⋆, c^π) < π/2` and `1` otherwise; the supremum is attained. -/
theorem lemma1_realized_worst_case_regret {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (cpi cstar : EuclideanSpace ℝ (Fin d)) (hcpi : cpi ∈ unitSphere d)
    (hcstar : cstar ∈ unitSphere d) :
    IsGreatest
      {r : ℝ | ∃ (X : Set (EuclideanSpace ℝ (Fin n)))
          (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
          (xpi xstar : EuclideanSpace ℝ (Fin n)),
          IsActionSet X ∧ IsContext f ∧ xpi ∈ argminSet cpi X f ∧
          xstar ∈ argminSet cstar X f ∧ r = inner ℝ (f xpi - f xstar) cstar}
      (regretCap (vecAngle cstar cpi)) := by sorry

end CtxInvOpt.Offline
