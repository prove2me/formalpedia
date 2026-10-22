-- Prove2me | Theorems.Thm_FollowCrowd_Inference_theta_mono_v
-- name    : FollowCrowd.Inference.theta_mono_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:14.329523+00:00
-- url     : https://prove2.me/theorems/2220694a-396a-4e30-b122-950f07e8c76a
-- title:
--   §4.2, p. 10 — θn(v) increases with v, so the interval of Proposition 2 is nonempty for each n
-- statement:
--   Under the standing assumptions, fix a queue length $n$ and let $\theta_n(v)$ be the belief under the threshold profile $p^-(v)$ (join at $\le\lfloor v\rfloor$, with probability $v-\lfloor v\rfloor$ at $\lfloor v\rfloor+1$). Then
--
--   1. $v \mapsto \theta_n(v)$ is strictly increasing on $[0, \bar N - 1]$;
--   2. if $\bar N \ge 2$, the interval of Proposition 2 is nonempty:
--   $$(n+1)\Bigl(\frac{\theta_n(\bar N-1)}{\mu_H} + \frac{1-\theta_n(\bar N-1)}{\mu_L}\Bigr) < (n+1)\Bigl(\frac{\theta_n(0)}{\mu_H} + \frac{1-\theta_n(0)}{\mu_L}\Bigr).$$
--
--   This is the paper's observation, from Lemma 2, that the inference effect makes the belief at each queue length grow with the other customers' joining threshold.
--
--   **Formalization Note** Beyond $v = \bar N - 1$ the profile changes only in the coordinate $\bar N$, which does not enter the law, so $\theta_n(v)$ is constant there; strict increase is claimed on $[0,\bar N - 1]$ only. $\bar N - 1$ is natural-number subtraction, cast to a real; $\bar N \ge 1$ under the standing assumptions.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), p. 10, §4.2, sentence after Proposition 2

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem theta_mono_v (P : Params) (hP : P.Standing) (n : ℕ) :
    StrictMonoOn (fun v => thetaV P v n) (Set.Icc 0 ((Nbar P - 1 : ℕ) : ℝ)) ∧
    (2 ≤ Nbar P →
      ((n : ℝ) + 1) * meanSojourn P (thetaV P ((Nbar P - 1 : ℕ) : ℝ) n) <
        ((n : ℝ) + 1) * meanSojourn P (thetaV P 0 n)) := by sorry

end FollowCrowd.Inference
