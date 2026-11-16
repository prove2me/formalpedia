-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_Supplement_lemma_8_4
-- name    : ConcurrentStochasticApprox.Approx.Supplement.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:23.585274+00:00
-- url     : https://prove2.me/theorems/ed3a10a6-c848-4422-94cc-c724f61c065f
-- title:
--   Lemma 8.4 (used in the proof of Theorem 4.1) — Exact separation from rational thresholds
-- statement:
--   Let $G,r,n,m,Q,B_Q$ satisfy the hypotheses of Lemma 8.3, including rewards in $[0,1]$, positive $Q\le2^{B_Q}$ and integer-multiple probabilities and rewards. Let $p,q,B_{\mathrm{inp}}$ be natural numbers with $p\le q$, $1\le q$ and $q\le2^{B_{\mathrm{inp}}}$, and set $\alpha=p/q$. With $B_{\mathrm{coef}}$ as in Lemma 8.3, put
--   $$B_\alpha=B_{\mathrm{coef}}+\left\lceil\log_2\left(m^n(B_{\mathrm{inp}}+3)\right)\right\rceil+1.$$
--   Then every state $s$ with $\operatorname{val}(s)\ne\alpha$ satisfies
--   $$|\operatorname{val}(s)-\alpha|\ge2^{-2^{B_\alpha}}.$$
--   Both threshold endpoints $0$ and $1$ are included. The explicit denominator condition includes all source thresholds using at most the given number of bits. This separation bound applies to the limit-average value and retains the source's exact double-exponential constant.
--
--   Differences from the source:
--   - generalization: a rational threshold p/q defined using at most B_inp bits, with 0 ≤ p ≤ q and q ≥ 1 → natural p ≤ q, 1 ≤ q and q ≤ 2^B_inp, without a numerator-plus-denominator bit restriction; reason: the source proof on printed 37 uses only this denominator bound, and every source threshold satisfies it
--   - encoding: 2 raised to the negative double-exponential exponent and base-two ceiling logarithms → (1/2)^(2^bAlpha) with Nat.clog 2 and m = max mA mB; reason: positive reciprocal powers express the same constant and follow the published base convention
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), Lemma 8.4, printed 36 (PDF 38)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Game
import Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_AlgebraicBounds

namespace ConcurrentStochasticApprox.Approx.Supplement

/-- Lemma 8.4 with the explicit denominator bound used on printed p. 37.
This includes every threshold whose numerator and denominator have at most Binp bits. -/
theorem lemma_8_4 {n mA mB : ℕ} (G : CSG n mA mB) (r : Reward n mA mB)
    (hr : IsReward r) (Q BQ : ℕ) (hQ : 0 < Q) (hQB : Q ≤ 2 ^ BQ)
    (hden : HasCommonDenom G r Q) (p q Binp : ℕ) (hq : 1 ≤ q) (hpq : p ≤ q)
    (hqB : q ≤ 2 ^ Binp) :
    ∀ s : Fin n, limAvgValue G r s ≠ (p : ℝ) / (q : ℝ) →
      (1 / 2 : ℝ) ^ (2 ^ bAlpha n (max mA mB) BQ Binp) ≤
        |limAvgValue G r s - (p : ℝ) / (q : ℝ)| := by sorry

end ConcurrentStochasticApprox.Approx.Supplement
