-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_lemma_A_1
-- name    : FlexGroupBuy.REE.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:39.537351+00:00
-- url     : https://prove2.me/theorems/07db5b5f-12ae-4bbe-a73e-444d683c0ffe
-- title:
--   Lemma A.1, Online Appendix p. 1 — with an increasing waiting time, a sign-up at state n persists at every later state n′ ≤ n
-- statement:
--   Consider a customer of valuation $v$ facing a premium price $p$ for a product of quality $\theta\ne 1$, a regular price $r$, and a waiting cost $c>0$ per unit time. Let $w(n)$ be the expected waiting time at pledge-to-go state $n$, increasing in $n$ on $\{1,\dots,N\}$. Signing up at state $n$ means that it is individually rational and incentive compatible:
--   $$
--   \theta v-p-c\,w(n)\ \ge\ 0,\qquad \theta v-p-c\,w(n)\ \ge\ v-r .
--   $$
--   If both hold at some state $n$ with $1\le n\le N$, then both hold at every subsequent state $n'$ with $1\le n'\le n$.
--
--   Taking $v=H$ or $v=L$ gives the statement for high-end and for low-end customers. The lemma underlies the classification of equilibrium segmentations by a single tipping state.
--
--   **Formalization Note.** The waiting time is a given function `w : ℕ → ℝ` monotone on $\{1,\dots,N\}$, the property the proof (Supplement p. 3) uses; in the paper $w$ is the equilibrium waiting time $w^G$. The hypothesis $\theta\ne1$ is kept as printed.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 1, Lemma A.1; proof Supplement pp. 3–4

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Lemma A.1 (Online Appendix p. 1): for a customer of valuation `v`, prices `p`, `r`, waiting cost
`c > 0` and an expected waiting time `w` increasing in the pledge-to-go state on `{1, …, N}`, if
signing up is individually rational and incentive compatible at state `n`, it is so at every
subsequent state `n' ≤ n`. -/
theorem lemma_A_1 (theta : ℝ) (htheta : theta ≠ 1) (N : ℕ) (v p r c : ℝ) (hc : 0 < c)
    (w : ℕ → ℝ) (hw : MonotoneOn w (Set.Icc 1 N)) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hIR : theta * v - p - c * w n ≥ 0) (hIC : theta * v - p - c * w n ≥ v - r) :
    ∀ n' : ℕ, 1 ≤ n' → n' ≤ n →
      theta * v - p - c * w n' ≥ 0 ∧ theta * v - p - c * w n' ≥ v - r := by sorry

end FlexGroupBuy.REE
