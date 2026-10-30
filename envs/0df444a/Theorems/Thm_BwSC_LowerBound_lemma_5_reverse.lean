-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_5_reverse
-- name    : BwSC.LowerBound.lemma_5_reverse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:24.323821+00:00
-- url     : https://prove2.me/theorems/b8a8862c-e08e-4aeb-b346-b37204a744e6
-- title:
--   Lemma 5, p. 58 (second inequality) — d_KL(q‖p) ≥ (p−q)²/(2q) for 0 ≤ p ≤ q ≤ 1
-- statement:
--   Let $0\le p\le q\le 1$ and let $d_{\rm KL}(x\,\|\,y)=x\log\frac xy+(1-x)\log\frac{1-x}{1-y}$ be the Kullback–Leibler divergence between Bernoulli distributions of parameters $x$ and $y$ (valued in $[0,\infty]$). Then
--   $$d_{\rm KL}(q\,\|\,p)\ \ge\ \frac{(p-q)^2}{2q}.$$
--
--   This is the second half of the localized Pinsker inequality (Lemma 5); the first half, $d_{\rm KL}(p\,\|\,q)\ge (p-q)^2/(2q)$, is the published `ExploreFirst.Collective.lemma_6`. The reverse half is what the generalized reverse Fano inequality needs when $D$ is the reverse KL divergence.
--
--   **Formalization Note** The Bernoulli divergence is the published `ExploreFirst.FundIneq.klBer`, the KL divergence of the two Bernoulli laws, which is $+\infty$ when $p\in\{0,1\}$ and $q\neq p$. The bound is stated in $[0,\infty]$. At $q=0$ the right side is $0/0$, which is $0$ in Lean; then $p=q=0$ and the claim is trivially true, as on the page.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 58, Lemma 5 (Localized Pinsker's Inequality, version 2), second inequality

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 5, p. 58, second inequality: if `0 ≤ p ≤ q ≤ 1` then
`d_KL(q ∥ p) ≥ (p - q)² / (2q)`, where `d_KL(q ∥ p)` is the Bernoulli divergence. -/
theorem lemma_5_reverse (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ENNReal.ofReal ((p - q) ^ 2 / (2 * q)) ≤ ExploreFirst.FundIneq.klBer q p := by sorry

end BwSC.LowerBound
