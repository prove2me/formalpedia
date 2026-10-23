-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_theorem_2
-- name    : ExplodingOffer.Mrl.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:42.938209+00:00
-- url     : https://prove2.me/theorems/d73645ee-39b4-476d-875f-e7fb4163e8f2
-- title:
--   Theorem 2, p. 16 — Π(s, t*_D(s)) is quasi-concave and (s*, t*_D) = (min{𝒯⁻¹(λT), ŝ}, t*_D(s*)) is the optimal package
-- statement:
--   Let $X$ be a nonnegative continuous random variable with support $[a,b]$ and finite mean $\bar x$, $\lambda > 0$, $T > 0$, $u > 0$, and let $\hat s$ be defined by (10). Then:
--
--   1. $s \mapsto \Pi(s, t_D^*(s))$ is quasi-concave on $[0, u]$;
--   2. the package
--   $$s^* = \min\{\mathcal T^{-1}(\lambda T),\ \hat s\}, \qquad t_D^* = t_D^*(s^*) = \big(T - \mathcal T(s^*)/\lambda\big)^+ \tag{12}$$
--   is an optimal solution of problem (7);
--   3. if $u \ne \bar x$ or $a = 0$, it is the only optimal solution of problem (7).
--
--   This is the paper's characterization of the proposer's optimal strategy: an exploding offer of size $\mathcal T^{-1}(\lambda T)$ when $\mathcal T^{-1}(\lambda T) \le \hat s$, and otherwise the offer $\hat s$ with a positive deadline.
--
--   **Formalization Note** "Characterized as follows" is read as existence and uniqueness of the optimal package. Uniqueness fails in the boundary case $u = \bar x$, $a > 0$, which the page does not exclude: there $\mathbb E[X \mid X \ge s] = \bar x = u$ for every $s \in [0, a]$, the surplus $\Pi(s, t_D^*(s))$ is constant on $[0, \min\{a, \mathcal T^{-1}(\lambda T)\}]$, and every size in that interval is optimal (for example, $X$ uniform on $[1,2]$ and $u = 3/2$). Part 3 therefore carries the condition $u \ne \bar x$ or $a = 0$. The quasi-concavity domain $[0, u]$ is the set of feasible sizes.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 16, Theorem 2, eq. (12)

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem theorem_2 {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u)
    {sh : ℝ} (hsh : IsSHat μ a b u sh) :
    QuasiconcaveOn ℝ (Set.Icc 0 u) (fun s => surplus μ b lam T u s (optDeadline μ b lam T s)) ∧
    IsOptimalPackage μ b lam T u (min (Tinv μ b (lam * T)) sh)
      (optDeadline μ b lam T (min (Tinv μ b (lam * T)) sh)) ∧
    ((u ≠ mean μ ∨ a = 0) → ∀ s tD : ℝ, IsOptimalPackage μ b lam T u s tD →
      s = min (Tinv μ b (lam * T)) sh ∧
      tD = optDeadline μ b lam T (min (Tinv μ b (lam * T)) sh)) := by sorry

end ExplodingOffer.Mrl
