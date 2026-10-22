-- Prove2me | Theorems.Thm_ContJRP_Align_claim_1_1_eoq_properties
-- name    : ContJRP.Align.claim_1_1_eoq_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:02.899446+00:00
-- url     : https://prove2.me/theorems/15b53b72-8451-4fae-b6ee-f4ae2d6391f5
-- title:
--   Claim 1.1, p. 2 — C(T) = K/T + HT is positive and strictly convex, √(K/H) is its unique minimizer, and C(θT*) = ½(θ + 1/θ)C(T*)
-- statement:
--   Let $K,H>0$ and $C(T)=K/T+HT$ for $T>0$. Then:
--
--   1. $C(T)>0$ for every $T>0$;
--   2. $C$ is strictly convex on $(0,\infty)$;
--   3. $T^*=\sqrt{K/H}>0$ minimizes $C$ over $(0,\infty)$, and it is the unique minimizer;
--   4. for every $\theta>0$,
--   $$C(\theta\cdot T^*)=\frac12\Big(\theta+\frac1\theta\Big)\cdot C(T^*).$$
--
--   These are the classical facts on the EOQ cost that the analysis of the easy policy and of the assignability bound (Lemma 3.6) rely on.
--
--   **Formalization Note** The positivity conjunct encodes the codomain $\mathbb R_{++}$ of the page's $C:(0,\infty)\to\mathbb R_{++}$; $K,H>0$ is what makes $\sqrt{K/H}$ the unique minimizer.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 2, Claim 1.1

import Mathlib
import Definitions.Def_ContJRP_Align_Model

namespace ContJRP.Align

theorem claim_1_1_eoq_properties (K H : ℝ) (hK : 0 < K) (hH : 0 < H) :
    (∀ T, 0 < T → 0 < eoqCost K H T) ∧
    StrictConvexOn ℝ (Set.Ioi 0) (eoqCost K H) ∧
    (0 < Real.sqrt (K / H) ∧ ∀ T, 0 < T → eoqCost K H (Real.sqrt (K / H)) ≤ eoqCost K H T) ∧
    (∀ T, 0 < T → eoqCost K H T = eoqCost K H (Real.sqrt (K / H)) → T = Real.sqrt (K / H)) ∧
    ∀ θ, 0 < θ → eoqCost K H (θ * Real.sqrt (K / H)) =
      1 / 2 * (θ + 1 / θ) * eoqCost K H (Real.sqrt (K / H)) := by sorry

end ContJRP.Align
