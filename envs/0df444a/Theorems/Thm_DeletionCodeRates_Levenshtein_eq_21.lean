-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_eq_21
-- name    : DeletionCodeRates.Levenshtein.eq_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:39.280606+00:00
-- url     : https://prove2.me/theorems/cbbfb8f1-901b-49d4-aa90-ac9468ab282c
-- title:
--   (21) — size and exponent of the run-restricted ensemble $\mathcal U(n,r)$
-- statement:
--   For $1\le r\le n$, $|\mathcal U(n,r)|=\binom{n-1}{r-1}$; and for $0<\rho<1$, $|\mathcal U(n,\lfloor\rho n\rfloor)|=2^{nh_2(\rho)+o(n)}$.
--
--   Differences from the source:
--   - encoding: 2^{n h₂(ρ)+o(n)} when r = ⌊ρn⌋ → ∃ ε : ℕ → ℝ, ε → 0, with |U(n, ⌊ρn⌋)| = 2^{n h₂(ρ) + n ε n} for all sufficiently large n; reason: o(n) = n·o(1); 'all sufficiently large n' because U(n, ⌊ρn⌋) is empty while ⌊ρn⌋ = 0, outside the paper's range 1 ≤ r
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), (21), p. 11 (PDF 13)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_DeletionCodeRates_Levenshtein_RunEnsemble

set_option autoImplicit false

open Filter Topology

namespace DeletionCodeRates.Levenshtein

/-- **(21)** (p. 11). For `1 ≤ r ≤ n`, `|U(n, r)| = C(n - 1, r - 1)`; and for `0 < ρ < 1`,
`|U(n, ⌊ρn⌋)| = 2^{n h₂(ρ) + o(n)}`: there is `ε_n → 0` with
`|U(n, ⌊ρn⌋)| = 2^{n h₂(ρ) + n ε_n}` for all sufficiently large `n`. -/
theorem eq_21 :
    (∀ n r : ℕ, 1 ≤ r → r ≤ n → (U n r).card = Nat.choose (n - 1) (r - 1)) ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ((U n ⌊ρ * n⌋₊).card : ℝ) =
        (2 : ℝ) ^ ((n : ℝ) * WildeQIT.binaryEntropy ρ + (n : ℝ) * ε n) := by sorry

end DeletionCodeRates.Levenshtein
