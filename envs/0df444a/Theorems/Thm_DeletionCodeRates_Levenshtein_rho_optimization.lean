-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_rho_optimization
-- name    : DeletionCodeRates.Levenshtein.rho_optimization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:19:47.872855+00:00
-- url     : https://prove2.me/theorems/c27326d2-7c97-4218-b713-bd6ec2442723
-- title:
--   Proof of Theorem 1 — run-density optimization $\sup_{0<\rho<1}\{h_2(\rho)+\rho\log_2y\}=\log_2(1+y)$
-- statement:
--   For fixed $y>0$,
--   $$\sup_{0<\rho<1}\{h_2(\rho)+\rho\log_2y\}=\log_2(1+y),$$
--   with the maximum attained at $\rho=y/(1+y)$.
--
--   Differences from the source:
--   - encoding: sup over 0 < ρ < 1, with the maximum attained at ρ = y/(1+y) → IsGreatest of the image of (0, 1), plus the value at ρ = y/(1+y); reason: IsGreatest says the value is attained and is an upper bound, i.e. a maximum
--   - encoding: 'for fixed x, y' with (x, y) ∈ D_del → for y > 0; reason: x does not occur in the identity; y > 0 is the y-range of D_del
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), proof of Theorem 1, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-- **Run-density optimization** (proof of Theorem 1, p. 15). For `y > 0`,
`sup_{0<ρ<1} {h₂(ρ) + ρ log₂ y} = log₂(1 + y)`, the maximum being attained at
`ρ = y / (1 + y)`. -/
theorem rho_optimization (y : ℝ) (hy : 0 < y) :
    IsGreatest ((fun ρ : ℝ => WildeQIT.binaryEntropy ρ + ρ * Real.logb 2 y) '' Set.Ioo 0 1)
      (Real.logb 2 (1 + y)) ∧
    WildeQIT.binaryEntropy (y / (1 + y)) + y / (1 + y) * Real.logb 2 y = Real.logb 2 (1 + y) := by sorry

end DeletionCodeRates.Levenshtein
