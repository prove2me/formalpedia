-- Prove2me | Theorems.Thm_AggGameNet_Sync_lemma_6
-- name    : AggGameNet.Sync.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:33:44.740159+00:00
-- url     : https://prove2.me/theorems/22614abf-9ef0-4979-a68d-7b5478040a94
-- title:
--   Lemma 6, p. 13 — summable geometric convolution
-- statement:
--   Let $(\zeta_k)_{k\ge0}$ be a nonnegative summable real sequence and let $0<\beta<1$. Then the geometric convolution is summable:
--
--   $$\sum_{k=0}^{\infty}\sum_{s=0}^{k}\beta^{k-s}\zeta_s<\infty.$$
--
--   The convergence argument applies this result with $\zeta_s=\alpha_s^2$ to control accumulated estimate error.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 6, p. 13

import Mathlib

namespace AggGameNet.Sync

/-- Lemma 6, p. 13: summability of a geometric convolution. -/
theorem lemma_6 (ζ : ℕ → ℝ) (hζ : ∀ k, 0 ≤ ζ k)
    (hsum : Summable ζ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun k => ∑ s ∈ Finset.range (k + 1), β ^ (k - s) * ζ s) := by sorry

end AggGameNet.Sync
