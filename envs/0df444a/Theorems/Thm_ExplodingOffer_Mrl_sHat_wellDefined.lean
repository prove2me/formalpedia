-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_sHat_wellDefined
-- name    : ExplodingOffer.Mrl.sHat_wellDefined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:40.781987+00:00
-- url     : https://prove2.me/theorems/880228ec-86b6-4dfd-9b11-c2f9f662f422
-- title:
--   §4.1, pp. 11–12 — E[X | X ≥ s] strictly increases on [a, b), equals x̄ at a; ŝ of (10) exists, is unique, and ŝ ≤ u
-- statement:
--   Let $X$ be a nonnegative continuous random variable with support $[a,b]$ and finite mean $\bar x$. Then:
--
--   1. $s \mapsto \mathbb E[X \mid X \ge s]$ is strictly increasing on $[a, b)$;
--   2. $\mathbb E[X \mid X \ge a] = \bar x$;
--   3. for every $u > 0$ there is exactly one $\hat s$ satisfying (10):
--   $$\hat s = \begin{cases} b, & u \ge b, \\ \text{the } s \in [a, b) \text{ with } \mathbb E[X \mid X \ge s] = u, & \bar x \le u < b, \\ 0, & u < \bar x; \end{cases}$$
--   4. $\hat s \le u$.
--
--   The size $\hat s$ is the offer at which the average competing alternative offer matches the proposer's utility; it is one of the two candidates in Theorem 2.
--
--   **Formalization Note** The page also says $\mathbb E[X \mid X \ge b] = b$; for continuous $X$ and finite $b$ this conditions on a null event and is a limit, so the monotonicity is stated on $[a, b)$ and the case $u = b$ of (10) is placed in the first case, which gives the same $\hat s = b$.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), pp. 11–12, §4.1, eq. (10) and the paragraph after it

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem sHat_wellDefined {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b) :
    StrictMonoOn (condMean μ) {s : ℝ | a ≤ s ∧ (s : EReal) < b} ∧
    condMean μ a = mean μ ∧
    (∀ u : ℝ, 0 < u → ∃! sh : ℝ, IsSHat μ a b u sh) ∧
    (∀ u sh : ℝ, 0 < u → IsSHat μ a b u sh → sh ≤ u) := by sorry

end ExplodingOffer.Mrl
