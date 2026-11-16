-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_Supplement_lemma_8_3
-- name    : ConcurrentStochasticApprox.Approx.Supplement.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:49.009794+00:00
-- url     : https://prove2.me/theorems/1a795410-3d6f-43e4-b1b9-dc437d84940c
-- title:
--   Lemma 8.3 (used in the proof of Theorem 4.1) — Algebraic values with exact coefficient bounds
-- statement:
--   Let $G$ be a concurrent stochastic game with $n\ge1$ states, $m=\max(|A|,|B|)\ge1$ and rewards $r:S\times A\times B\to[0,1]$. Suppose every probability and reward is an integer multiple of $1/Q$, where $Q$ is a positive integer and $Q\le2^{B_Q}$. Put
--   $$B_{\mathrm{coef}}=\left\lceil\log_2\left(4nm^n(\lceil\log_2 n\rceil+n\lceil\log_2 m\rceil+B_Q+3)\right)\right\rceil.$$
--   For each state $s$, there exist an integer $d\le m^n$ and integer coefficients $e_0,\ldots,e_d$ such that
--   $$e_d\ne0,\qquad\sum_{i=0}^d e_i\operatorname{val}(s)^i=0,\qquad |e_i|<2^{2^{B_{\mathrm{coef}}}}\quad(0\le i\le d).$$
--   Here $\operatorname{val}$ is the limit-average value for unrestricted full-history behavioural strategies. The nonzero leading coefficient makes the polynomial nonzero. This gives the algebraic size bound used for rational-threshold separation.
--
--   Differences from the source:
--   - encoding: at most m actions per player, coefficients e_0 through e_d and base-two ceiling logarithms → m = max mA mB, coefficients indexed by Fin (d + 1), and Nat.clog 2; reason: uses the actual maximum action count and the published Lemma 7.2 convention without changing any bound
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), Lemma 8.3, printed 36 (PDF 38)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Game
import Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_AlgebraicBounds
open Finset

namespace ConcurrentStochasticApprox.Approx.Supplement

/-- Lemma 8.3, including the exact degree, nonzero leading coefficient and strict coefficient bound. -/
theorem lemma_8_3 {n mA mB : ℕ} (G : CSG n mA mB) (r : Reward n mA mB)
    (hr : IsReward r) (Q BQ : ℕ) (hQ : 0 < Q) (hQB : Q ≤ 2 ^ BQ)
    (hden : HasCommonDenom G r Q) :
    ∀ s : Fin n, ∃ d : ℕ, d ≤ (max mA mB) ^ n ∧
      ∃ e : Fin (d + 1) → ℤ, e ⟨d, Nat.lt_succ_self d⟩ ≠ 0 ∧
        (∑ i : Fin (d + 1), (e i : ℝ) * limAvgValue G r s ^ (i : ℕ)) = 0 ∧
        ∀ i, |e i| < (2 : ℤ) ^ (2 ^ bCoef n (max mA mB) BQ) := by sorry

end ConcurrentStochasticApprox.Approx.Supplement
