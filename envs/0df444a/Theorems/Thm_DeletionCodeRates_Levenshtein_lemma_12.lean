-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_lemma_12
-- name    : DeletionCodeRates.Levenshtein.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:21:22.224017+00:00
-- url     : https://prove2.me/theorems/59956a21-f289-49ef-be5d-71f66ceaf067
-- title:
--   Lemma 12 — fixed-witness generating function
-- statement:
--   For a nonempty binary witness $\boldsymbol w=w_1\cdots w_\ell$ with $w_1=0$,
--   $$F_{\boldsymbol w}(x,y)=y\prod_{j=2}^{\ell}G_{w_{j-1},w_j}(x,y)\,T_{\mathrm{tail}}(x,y),\qquad(24)$$
--   where $G_{a,b}=G_s$ if $a=b$ and $G_{a,b}=G_f$ otherwise.
--
--   Differences from the source:
--   - encoding: F_w as the sum (22) over all finite words starting with 0 and containing w → the power series Fw w whose coefficient of x^d y^r is |{c ∈ U(ℓ+d, r) : w ⪯ c}|; reason: the terms of (22) grouped by monomial: words of length ℓ+d starting with 0 with r runs form U(ℓ+d, r)
--   - encoding: the rational functions G_s, G_f, T_tail and the product over j = 2..ℓ → MvPowerSeries over ℚ with power-series inverses of 1 − x and 1 − x(1+y); the product over consecutive pairs of w (w.zip w.tail); reason: the paper's formal expansions; same series
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), Lemma 12, p. 13 (PDF 15)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_GenFun

set_option autoImplicit false

open MvPowerSeries

namespace DeletionCodeRates.Levenshtein

/-- **Lemma 12** (fixed witness subsequence, p. 13). For a nonempty binary witness
`w = w₁ ⋯ w_ℓ` with `w₁ = 0`, `F_w(x, y) = y ∏_{j=2}^{ℓ} G_{w_{j-1}, w_j}(x, y) T_tail(x, y)` (24),
where `G_{a,b} = G_s` if `a = b` and `G_f` otherwise; here `x = X 0`, `y = X 1`. -/
theorem lemma_12 (w : List (Fin 2)) (hw : w.head? = some 0) :
    Fw w = X 1 * ((w.zip w.tail).map (fun p => Gtrans p.1 p.2)).prod * Ttail (X 0) (X 1) := by sorry

end DeletionCodeRates.Levenshtein
