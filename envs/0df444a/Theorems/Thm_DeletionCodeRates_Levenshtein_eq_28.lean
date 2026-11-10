-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_eq_28
-- name    : DeletionCodeRates.Levenshtein.eq_28
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:21:23.872921+00:00
-- url     : https://prove2.me/theorems/707702d8-ba49-4d15-9ba9-471d88eaa2bf
-- title:
--   (28) — positivity, eigenvalues and Perron value of the diagonal transfer matrix
-- statement:
--   For $x\in(0,1)$ and $y>0$, with the local factors evaluated at $(x,y)$, $S_1=G_s^2-(G_s^+)^2$ and $F_1=G_f^2-(G_f^+)^2$ are both positive. The two eigenvalues of $\mathbf T^{(1)}_{\mathrm{del}}(x,y)=\begin{pmatrix}S_1&F_1\\F_1&S_1\end{pmatrix}$ are $S_1+F_1$ and $S_1-F_1$, so
--   $$\lambda^{(1)}_{\mathrm{del}}(x,y)=\lambda(\mathbf T^{(1)}_{\mathrm{del}}(x,y))=S_1+F_1=1+y^2\frac{1+3x}{1-x}.\qquad(28)$$
--
--   Differences from the source:
--   - encoding: the two eigenvalues are S₁ + F₁ and S₁ − F₁ → charpoly T = (X − C(S₁+F₁))(X − C(S₁−F₁)); reason: the eigenvalues of a matrix are the roots of its characteristic polynomial
--   - encoding: λ(T) = S₁ + F₁ (spectral radius) → |S₁ − F₁| ≤ S₁ + F₁ together with the factorization; reason: the spectral radius is the largest modulus of an eigenvalue
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), (27)–(28), p. 14 (PDF 16)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RateFunctions
import Definitions.Def_DeletionCodeRates_Levenshtein_DiagonalEval

set_option autoImplicit false

open Polynomial

namespace DeletionCodeRates.Levenshtein

/-- **(28)** (p. 14). For `x ∈ (0, 1)` and `y > 0`, with `S₁ = G_s² - (G_s⁺)²` and
`F₁ = G_f² - (G_f⁺)²` evaluated at `(x, y)`: both `S₁` and `F₁` are positive; the eigenvalues of
`T^{(1)}_del(x, y) = [[S₁, F₁], [F₁, S₁]]` are `S₁ + F₁` and `S₁ - F₁` (its characteristic
polynomial is `(X - (S₁ + F₁))(X - (S₁ - F₁))`), so its spectral radius is `S₁ + F₁`
(`|S₁ - F₁| ≤ S₁ + F₁`); and `λ^{(1)}_del(x, y) = S₁ + F₁ = 1 + y² (1 + 3x) / (1 - x)`. -/
theorem eq_28 (x y : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hy : 0 < y) :
    0 < S1R x y ∧ 0 < F1R x y ∧
    (TdelR x y).charpoly = (X - C (S1R x y + F1R x y)) * (X - C (S1R x y - F1R x y)) ∧
    |S1R x y - F1R x y| ≤ S1R x y + F1R x y ∧
    S1R x y + F1R x y = lambdaDel x y := by sorry

end DeletionCodeRates.Levenshtein
