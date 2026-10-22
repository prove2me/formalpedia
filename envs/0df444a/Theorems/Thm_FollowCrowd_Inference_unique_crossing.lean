-- Prove2me | Theorems.Thm_FollowCrowd_Inference_unique_crossing
-- name    : FollowCrowd.Inference.unique_crossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:17.687357+00:00
-- url     : https://prove2.me/theorems/a2059665-8b53-4e9f-881f-e0f0602e071e
-- title:
--   Proof of Proposition 2, Online Appendix p. 1 — u(n, v) increases in v; the interval condition ⇔ u(n,0) < 0 < u(n,N̄−1); then a unique zero v ∈ (0, N̄−1)
-- statement:
--   Under the standing assumptions, fix a queue length $n$ and write $u(n,v) = R - C(n+1)\bigl[\theta_n(v)/\mu_H + (1-\theta_n(v))/\mu_L\bigr]$ for the utility of joining under the threshold profile $p^-(v)$. Then
--
--   1. $v\mapsto u(n,v)$ is strictly increasing on $[0,\bar N-1]$ and non-decreasing on $[0,\infty)$;
--   2. the condition
--   $$(n+1)\Bigl(\frac{\theta_n(\bar N-1)}{\mu_H}+\frac{1-\theta_n(\bar N-1)}{\mu_L}\Bigr) < \frac RC < (n+1)\Bigl(\frac{\theta_n(0)}{\mu_H}+\frac{1-\theta_n(0)}{\mu_L}\Bigr)$$
--   holds if and only if $u(n,0) < 0$ and $u(n,\bar N-1) > 0$;
--   3. if $u(n,0) < 0 < u(n,\bar N-1)$, there is a unique $v \in (0,\bar N-1)$ with $u(n,v) = 0$.
--
--   The zero $v$ is the other customers' threshold at which the tagged customer starts to join at queue length $n$.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), Online Appendix p. 1 (PDF 25), proof of Proposition 2, first three sentences

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem unique_crossing (P : Params) (hP : P.Standing) (n : ℕ) :
    StrictMonoOn (fun v => utilV P v n) (Set.Icc 0 ((Nbar P - 1 : ℕ) : ℝ)) ∧
    MonotoneOn (fun v => utilV P v n) (Set.Ici 0) ∧
    (((n : ℝ) + 1) * meanSojourn P (thetaV P ((Nbar P - 1 : ℕ) : ℝ) n) < P.R / P.C ∧
        P.R / P.C < ((n : ℝ) + 1) * meanSojourn P (thetaV P 0 n) ↔
      utilV P 0 n < 0 ∧ 0 < utilV P ((Nbar P - 1 : ℕ) : ℝ) n) ∧
    (utilV P 0 n < 0 → 0 < utilV P ((Nbar P - 1 : ℕ) : ℝ) n →
      ∃! v, v ∈ Set.Ioo 0 ((Nbar P - 1 : ℕ) : ℝ) ∧ utilV P v n = 0) := by sorry

end FollowCrowd.Inference
