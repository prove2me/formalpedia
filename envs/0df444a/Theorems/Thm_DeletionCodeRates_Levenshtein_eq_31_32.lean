-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_eq_31_32
-- name    : DeletionCodeRates.Levenshtein.eq_31_32
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:21:24.628627+00:00
-- url     : https://prove2.me/theorems/dd894187-9cc3-46ff-ae38-6d009676b81e
-- title:
--   (31)–(32) — positive evaluation bound on $M_1(n,d;r)$
-- statement:
--   For any fixed $(x,y)\in\mathcal D_{\mathrm{del}}$,
--   $$M_1(n,d;r)\le A_1(x,y)\,\lambda^{(1)}_{\mathrm{del}}(x,y)^{n-d-1}x^{-2d}y^{-2r},\qquad A_1(x,y)=\Big(\frac{y}{1-x(1+y)}\Big)^2,\qquad(31)$$
--   and for $r=\lfloor\rho n\rfloor$, $d=\lfloor\delta n\rfloor$,
--   $$M_1(n,d;r)\le2^{n\Phi_{1,\delta,\rho}(x,y)+o(n)}.\qquad(32)$$
--
--   Differences from the source:
--   - generalization: (31) for 0 ≤ d < n and 1 ≤ r ≤ n (the range of (25)) → (31) for all n, d, r ∈ ℕ; reason: outside that range M₁(n, d; r) = 0 (no word of length n − d starts with 0 when d ≥ n; U(n, r) is empty for r = 0 or r > n) while the right side is positive; the statement specializes to the source's range
--   - generalization: (32) for the paper's 0 < δ < 1/2 and 0 < ρ < 1 → (32) for all δ ≥ 0, ρ ≥ 0; reason: the source's parameters are a special case
--   - encoding: 2^{nΦ + o(n)} → ∃ ε : ℕ → ℝ, ε → 0, with M₁ ≤ 2^{nΦ + n ε n} for every n; reason: o(n) = n·o(1); M₁ = 0 at n = 0, and finitely many positive n can be absorbed in ε n
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), (31)–(32), p. 15 (PDF 17)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RateFunctions
import Definitions.Def_DeletionCodeRates_Levenshtein_Witness
import Definitions.Def_DeletionCodeRates_Levenshtein_DiagonalEval

set_option autoImplicit false

open Filter Topology

namespace DeletionCodeRates.Levenshtein

/-- **(31)–(32)** (p. 15). For every fixed `(x, y) ∈ D_del`:
(31) `M₁(n, d; r) ≤ A₁(x, y) λ^{(1)}_del(x, y)^{n-d-1} x^{-2d} y^{-2r}` with
`A₁(x, y) = (y / (1 - x(1 + y)))²`; and (32) for `r = ⌊ρn⌋`, `d = ⌊δn⌋`,
`M₁(n, d; r) ≤ 2^{n Φ_{1,δ,ρ}(x, y) + o(n)}`, i.e. there is `ε_n → 0` with
`M₁(n, ⌊δn⌋; ⌊ρn⌋) ≤ 2^{n Φ_{1,δ,ρ}(x, y) + n ε_n}` for every `n`. -/
theorem eq_31_32 (x y : ℝ) (hxy : (x, y) ∈ Ddel) :
    (∀ n d r : ℕ, (M1 n d r : ℝ) ≤
      A1R x y * lambdaDel x y ^ (n - d - 1) * (x ^ (2 * d))⁻¹ * (y ^ (2 * r))⁻¹) ∧
    ∀ δ ρ : ℝ, 0 ≤ δ → 0 ≤ ρ → ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, (M1 n ⌊δ * n⌋₊ ⌊ρ * n⌋₊ : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * Phi δ ρ x y + (n : ℝ) * ε n) := by sorry

end DeletionCodeRates.Levenshtein
