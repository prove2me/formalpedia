-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_theorem_13
-- name    : DeletionCodeRates.Levenshtein.theorem_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:21:25.237526+00:00
-- url     : https://prove2.me/theorems/33834e47-fb41-44b1-889f-2f677a382a90
-- title:
--   Theorem 13 — two-codeword transfer-matrix generating function, and the bad-pair bound (26)
-- statement:
--   Let $S_1,F_1,\mathbf T^{(1)}_{\mathrm{del}},Q_1,A_1$ be as in Theorem 13 (four variables $x_1,y_1,x_2,y_2$), $\boldsymbol e_0=(1,0)^T$ and $\mathbf 1=(1,1)^T$. For $0\le d<n$ and $1\le r\le n$,
--   $$M_1(n,d;r)=[x_1^dx_2^dy_1^ry_2^r]\,A_1\boldsymbol e_0^T(\mathbf T^{(1)}_{\mathrm{del}})^{n-d-1}\mathbf 1=[x_1^dx_2^dy_1^ry_2^r]\,A_1Q_1^{n-d-1},\qquad(25)$$
--   and, for two independent uniform samples from $\mathcal U(n,r)$,
--   $$\Pr(E_{\{1,2\}})\le\frac{M_1(n,d;r)}{|\mathcal U(n,r)|^2}.\qquad(26)$$
--
--   Differences from the source:
--   - encoding: e₀ᵀ (T^{(1)}_del)^{n−d−1} 𝟙 → ∑ j, (Tdel ^ (n − d − 1)) 0 j; reason: the first row sum of the matrix power is e₀ᵀ M 𝟙
--   - encoding: Pr(E_{1,2}) for independent uniform C₁, C₂ ∈ U(n, r) → probBadPair n d r = |{(c₁, c₂) ∈ U(n,r)² : LCS(c₁, c₂) ≥ n − d}| / |U(n,r)|²; reason: the uniform product law on U(n, r)²
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), Theorem 13, p. 14 (PDF 16)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RunEnsemble
import Definitions.Def_DeletionCodeRates_Levenshtein_Witness
import Definitions.Def_DeletionCodeRates_Levenshtein_GenFun

set_option autoImplicit false

open MvPowerSeries

namespace DeletionCodeRates.Levenshtein

/-- **Theorem 13** (the two-codeword transfer-matrix generating function, p. 14). For
`0 ≤ d < n` and `1 ≤ r ≤ n`, (25):
`M₁(n, d; r) = [x₁^d x₂^d y₁^r y₂^r] A₁ e₀ᵀ (T^{(1)}_del)^{n-d-1} 𝟙 = [x₁^d x₂^d y₁^r y₂^r] A₁ Q₁^{n-d-1}`
with `e₀ = (1, 0)ᵀ`, `𝟙 = (1, 1)ᵀ`; and (26): `Pr(E_{1,2}) ≤ M₁(n, d; r) / |U(n, r)|²` for two
independent uniform samples from `U(n, r)`. -/
theorem theorem_13 (n d r : ℕ) (hd : d < n) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    ((M1 n d r : ℚ) = coeff (mono4 d r) (A1 * ∑ j : Fin 2, (Tdel ^ (n - d - 1)) 0 j)) ∧
    ((M1 n d r : ℚ) = coeff (mono4 d r) (A1 * Q1 ^ (n - d - 1))) ∧
    probBadPair n d r ≤ (M1 n d r : ℝ) / ((U n r).card : ℝ) ^ 2 := by sorry

end DeletionCodeRates.Levenshtein
