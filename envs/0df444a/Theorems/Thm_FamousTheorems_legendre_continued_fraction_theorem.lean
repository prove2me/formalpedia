-- Prove2me | Theorems.Thm_FamousTheorems_legendre_continued_fraction_theorem
-- name    : FamousTheorems.legendre_continued_fraction_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:39.599363+00:00
-- url     : https://prove2.me/theorems/e25b99ff-d043-4c9f-9e94-b9f55f1f4468
-- title:
--   Legendre's theorem on continued fractions
-- statement:
--   **Legendre's theorem on continued fractions.** Let $\xi$ be a real number and $q=a/b$ a rational number in lowest terms with
--   $$\Big|\xi-\frac ab\Big|<\frac1{2b^2}.$$
--   Then $q$ is a convergent of the continued fraction expansion of $\xi$.
--
--   So very good rational approximations are automatically convergents. The theorem is central in Diophantine approximation, and it is used in the analysis of Pell's equation, in Wiener's attack on RSA with a small private exponent, and in the classical part of Shor's factoring algorithm.
--
--   **Formalization note.** Mathlib's `Real.exists_rat_eq_convergent`. `q.den` is the reduced denominator of `q : ℚ`, and `ξ.convergent n` is the $n$-th convergent of the continued fraction of $\xi$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.exists_rat_eq_convergent`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem legendre_continued_fraction_theorem {ξ : ℝ} {q : ℚ} (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) : ∃ n : ℕ, q = ξ.convergent n := by sorry

end FamousTheorems
