-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_2_2
-- name    : DictatorsCK.Main.lemma_2_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T06:32:19.799061+00:00
-- url     : https://prove2.me/theorems/262e3ce8-318c-4294-8723-aea6f70ba279
-- title:
--   Lemma 2.2 — a continuous function with nonnegative derivative wherever it is positive, and $G(b)\le0$, is $\le0$ on $[a,b]$
-- statement:
--   Let $a<b$ and let $G:[a,b]\to\mathbb R$ be continuous on $[a,b]$ and differentiable on $(a,b)$, with $G(b)\le0$. If $G'(x)\ge0$ for every $x\in(a,b)$ with $G(x)>0$, then $G(x)\le0$ for every $x\in[a,b]$.
--
--   This endpoint principle turns "a positive gap has a positive derivative" into the inequality $G_f\le0$ near the noiseless endpoint.
--
--   Differences from the source:
--   - encoding: G : [a, b] → ℝ and its derivative G′ on (a, b) → G : ℝ → ℝ, with continuity on Icc a b, differentiability on Ioo a b and G′(x) = deriv G x; reason: values of G outside [a, b] enter no hypothesis or conclusion, and at interior points deriv G is the derivative of the restriction
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 10 (PDF 11), Lemma 2.2

import Mathlib

namespace DictatorsCK.Main

theorem lemma_2_2 (a b : ℝ) (hab : a < b) (G : ℝ → ℝ) (hcont : ContinuousOn G (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ G (Set.Ioo a b)) (hGb : G b ≤ 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < G x → 0 ≤ deriv G x) :
    ∀ x ∈ Set.Icc a b, G x ≤ 0 := by sorry

end DictatorsCK.Main
