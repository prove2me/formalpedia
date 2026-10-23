-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_qStar_solves_10
-- name    : CustomerVoice.OLearn.qStar_solves_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:45.23199+00:00
-- url     : https://prove2.me/theorems/bfa3dc03-7e3d-49c4-94b1-a28e01cb2d73
-- title:
--   §3.3, p. 16, (10) — the buyer's first-best request under symmetric information is q*(θ) = min{γθ/(s+γk), θ/(2k)}
-- statement:
--   Under the standing assumptions, fix a buyer type with preference $\theta\in\{\theta_H,\theta_L\}$ known to the seller, and let $\bar q(\theta)=\gamma\theta/(s+\gamma k)$ be the largest acceptable request. Then $q^*(\theta)=\min\{\gamma\theta/(s+\gamma k),\theta/(2k)\}$ lies in $[0,\bar q(\theta)]$ and is the unique maximizer on that interval of the buyer's payoff (10):
--   $$q^*(\theta)\in\operatorname*{arg\,max}_{0\le q\le \bar q(\theta)} \mu(q,\theta,\theta),\qquad \mu(q,\theta,\theta)=\mu(q^*(\theta),\theta,\theta),\ 0\le q\le\bar q(\theta)\ \Longrightarrow\ q=q^*(\theta).$$
--
--   This identifies the cheap-signaling requests $q^O_H$, $q^O_L$ as the buyers' full-information optima.
--
--   **Formalization Note** The payoff is $\mu$ of (9), with both $\max\{\cdot,0\}$ terms. On the constraint set it equals $(1-\gamma)(\theta q-kq^2)$, as (10) writes. Uniqueness of the maximizer is added because the sibling mission on the absence of other separating equilibria uses it; it is part of what "This yields" asserts.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 16, §3.3, (10)

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem qStar_solves_10 (M : Model) (hM : M.Standing) (t : CustomerVoice.ALearn.BType) :
    M.qStar (M.θ t) ∈ Set.Icc 0 (M.γ * M.θ t / (M.s + M.γ * M.k)) ∧
    IsMaxOn (fun q => M.mu q (M.θ t) (M.θ t))
      (Set.Icc 0 (M.γ * M.θ t / (M.s + M.γ * M.k))) (M.qStar (M.θ t)) ∧
    (∀ q ∈ Set.Icc 0 (M.γ * M.θ t / (M.s + M.γ * M.k)),
      M.mu q (M.θ t) (M.θ t) = M.mu (M.qStar (M.θ t)) (M.θ t) (M.θ t) →
        q = M.qStar (M.θ t)) := by sorry

end CustomerVoice.OLearn
