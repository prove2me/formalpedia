-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_eq_33
-- name    : DeletionCodeRates.Levenshtein.eq_33
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:46.826019+00:00
-- url     : https://prove2.me/theorems/a636c0e5-81a4-41c5-a739-3f932a6bfaae
-- title:
--   (33) — the explicit point $(\delta,1)$: $R^{(1)}_{\mathrm{del}}(\delta)\ge R_{\mathrm{Lev}}(\delta)-(1-\delta)\log_2(1-\delta^2)>R_{\mathrm{Lev}}(\delta)$
-- statement:
--   For $0<\delta<1/2$, the point $(x,y)=(\delta,1)$ is feasible, $\lambda^{(1)}_{\mathrm{del}}(\delta,1)=\frac{2(1+\delta)}{1-\delta}=\frac{2(1-\delta^2)}{(1-\delta)^2}$, and
--   $$R^{(1)}_{\mathrm{del}}(\delta)\ge1+\delta-2h_2(\delta)-(1-\delta)\log_2(1-\delta^2)>R_{\mathrm{Lev}}(\delta).\qquad(33)$$
--
--   Differences from the source: none.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), (33), p. 15 (PDF 17)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_DeletionCodeRates_Levenshtein_RateFunctions

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-- **(33)** (p. 15). For `0 < δ < 1/2`, the point `(x, y) = (δ, 1)` is feasible,
`λ^{(1)}_del(δ, 1) = 2(1 + δ)/(1 - δ) = 2(1 - δ²)/(1 - δ)²`, and
`R^{(1)}_del(δ) ≥ 1 + δ - 2h₂(δ) - (1 - δ) log₂(1 - δ²) > R_Lev(δ)`. -/
theorem eq_33 (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    (δ, (1 : ℝ)) ∈ Ddel ∧
    lambdaDel δ 1 = 2 * (1 + δ) / (1 - δ) ∧
    2 * (1 + δ) / (1 - δ) = 2 * (1 - δ ^ 2) / (1 - δ) ^ 2 ∧
    1 + δ - 2 * WildeQIT.binaryEntropy δ - (1 - δ) * Real.logb 2 (1 - δ ^ 2) ≤ RDel δ ∧
    RLev δ < 1 + δ - 2 * WildeQIT.binaryEntropy δ - (1 - δ) * Real.logb 2 (1 - δ ^ 2) := by sorry

end DeletionCodeRates.Levenshtein
