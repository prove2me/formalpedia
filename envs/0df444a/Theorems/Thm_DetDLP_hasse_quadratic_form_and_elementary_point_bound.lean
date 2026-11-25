-- Prove2me | Theorems.Thm_DetDLP_hasse_quadratic_form_and_elementary_point_bound
-- name    : DetDLP.hasse_quadratic_form_and_elementary_point_bound
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T14:02:53.550245+00:00
-- url     : https://prove2.me/theorems/6db1c51a-c63f-4698-bced-573e00bf108e
-- title:
--   Elementary Elliptic-Curve Point-Count Bound and Hasse–Cauchy–Schwarz Quadratic-Form Deduction
-- statement:
--   Establishes the two algebraic pillars of Hasse's elliptic-curve point-count estimate over $\mathbb{F}_p$:
--
--   1. **Elementary fiber bound:** for every prime $p$ and Weierstrass curve $E / \mathbb{F}_p$, each $x \in \mathbb{F}_p$ has at most two affine points $(x, y) \in E(\mathbb{F}_p)$, so $1 \le \#E(\mathbb{F}_p) \le 2p + 1$;
--   2. **Hasse–Cauchy–Schwarz degree-form deduction:** for any integer $p > 0$ and point count $N$, if the Frobenius-identity endomorphism degree quadratic form $$Q(m, n) = m^2 p - m n (p + 1 - N) + n^2$$ is nonnegative on $\mathbb{Z} \times \mathbb{Z}$, then evaluating at $(m, n) = (p + 1 - N, 2p)$ yields $(N - (p + 1))^2 \le 4p$ and $|N - (p + 1)| \le 2\sqrt{p}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1 (p. 11)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- Algebraic core of Hasse's elliptic-curve point-count bound (Section 3.1, p. 11):
1. Elementary fiber bound: for every prime `p` and Weierstrass curve `E / F_p`, each `x ∈ F_p`
   has at most 2 affine points `(x, y) ∈ E(F_p)`, so `1 ≤ #E(F_p) ≤ 2p + 1`.
2. Hasse–Cauchy–Schwarz degree-form deduction: for any `p > 0` and point count `N`, nonnegativity
   of the Frobenius-identity degree quadratic form
   `Q(m, n) = deg(m φ_p - n id_E) = m^2 p - m n (p + 1 - N) + n^2 ≥ 0` on `ℤ × ℤ`
   implies `(N - (p + 1))^2 ≤ 4p` and `|N - (p + 1)| ≤ 2 √p`. -/
theorem hasse_quadratic_form_and_elementary_point_bound :
    (∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)),
      letI := ecPointFintype E
      1 ≤ Fintype.card E.toAffine.Point ∧ Fintype.card E.toAffine.Point ≤ 2 * p + 1) ∧
    (∀ (p N : ℕ), 0 < p →
      (∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * ((p : ℤ) + 1 - (N : ℤ)) + n ^ 2) →
      ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) ∧
      |(N : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) := by
  sorry

end DetDLP
