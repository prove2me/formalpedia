-- Prove2me | Theorems.Thm_AssortRotation_Concealment_remark_1
-- name    : AssortRotation.Concealment.remark_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:14.588147+00:00
-- url     : https://prove2.me/theorems/b57ff01f-a22f-4bf3-9ac3-089b875a0e65
-- title:
--   Remark 1, p. 12 — appending a product never lowers the sequential revenue $R^s$
-- statement:
--   Products are offered sequentially to a consumer with nonnegative, decreasing marginal utility $v$, who buys product $i$ iff $v(k)+X_i-p_i\ge0$ with $k$ her past purchases. Let $R^s(M)$ be the revenue from a sequence of $M$ products. Appending a further product $(p_{M+1},X_{M+1})$ with $p_{M+1}\ge 0$ at the end cannot decrease the revenue:
--   $$
--   R^s(M)\ \le\ R^s(M+1).
--   $$
--
--   Consequently an optimized sequential assortment may be taken to include all $N$ products. The optimized sequential revenue $\mathbb E[R^s_*]$ is therefore a maximum over orders of all $N$ products.
--
--   **Formalization Note.** The statement is pathwise, for an arbitrary list of (price, shock) pairs.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 12, Remark 1

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

/-- Remark 1, p. 12. Appending one more product (with a nonnegative price) at the end of a
sequential assortment never lowers the sequential revenue `R^s` of (6). -/
theorem remark_1 (v : ℕ → ℝ) (hv : MarginalUtility v) (L : List (ℝ × ℝ)) (a : ℝ × ℝ)
    (ha : 0 ≤ a.1) :
    seqRev v L 0 ≤ seqRev v (L ++ [a]) 0 := by sorry

end AssortRotation.Concealment
