-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_lemma_1
-- name    : ExplodingOffer.Mrl.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:38.317275+00:00
-- url     : https://prove2.me/theorems/5dd9b141-ddc5-451b-8ff0-674322590620
-- title:
--   Lemma 1, pp. 7–8 — the value-to-go (2) is the solution of the HJB (18), and v(t_D) = 𝒯⁻¹(λ(T − t_D)) < b
-- statement:
--   Let $X$ be a nonnegative continuous random variable with support $[a,b]$ and finite mean, let $\lambda > 0$, $T > 0$, and let $(s, t_D)$ be an offer package with $0 \le t_D \le T$ and $s \ge v(t_D) = \mathcal T^{-1}(\lambda(T - t_D))$. Let
--   $$V(t; s, t_D) = \begin{cases} \mathcal T^{-1}\big(\mathcal T(s) + \lambda(t_D - t)\big), & 0 \le t \le t_D, \\ \mathcal T^{-1}\big(\lambda(T - t)\big), & t_D < t \le T, \end{cases}$$
--   when $s < b$, and $V(t; s, t_D) = s$ on $[0, t_D]$ (and $\mathcal T^{-1}(\lambda(T-t))$ on $(t_D, T]$) when $s \ge b$. Then:
--
--   1. $V(\cdot\,; s, t_D)$ solves the HJB system (18): $V'(t) = -\lambda \mathcal L(V(t))$ on $[0,t_D) \cup (t_D,T)$, $V(t_D) = s$, $V(T) = 0$ (if $t_D < T$), with $V$ continuous on $[0, t_D]$ and on $(t_D, T]$;
--   2. it is the only solution: every solution of (18) coincides with it on $[0, T]$;
--   3. $v(t_D) = \mathcal T^{-1}(\lambda(T - t_D)) < b$;
--   4. if $t_D < T$, then $V(t; s, t_D) \to v(t_D)$ as $t \downarrow t_D$, so $v(t_D)$ is the right limit of the value-to-go at the deadline.
--
--   This identifies the responder's expected value of continuing the search, the basis of every later result.
--
--   **Formalization Note** The page defines $V$ through the limit of the recursion (1) and states (18) in the proof; here "characterized as follows" is formalized as existence and uniqueness for (18). At $t_D = T$ the printed (18) demands $V(T) = s$ and $V(T) = 0$; the terminal condition $V(T) = 0$ is imposed only for $t_D < T$. The hypotheses $\lambda > 0$, $T > 0$ and finite mean are standing assumptions of the mission.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), pp. 7–8, Lemma 1, eqs. (2), (3); p. 33, eq. (18)

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem lemma_1 {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    {s tD : ℝ} (htD0 : 0 ≤ tD) (htDT : tD ≤ T) (hs : minAccept μ b lam T tD ≤ s) :
    IsHJB μ lam T s tD (valueToGo μ b lam T s tD) ∧
    (∀ V : ℝ → ℝ, IsHJB μ lam T s tD V →
      ∀ t ∈ Set.Icc 0 T, V t = valueToGo μ b lam T s tD t) ∧
    (minAccept μ b lam T tD : EReal) < b ∧
    (tD < T → Filter.Tendsto (valueToGo μ b lam T s tD) (nhdsWithin tD (Set.Ioi tD))
      (nhds (minAccept μ b lam T tD))) := by sorry

end ExplodingOffer.Mrl
