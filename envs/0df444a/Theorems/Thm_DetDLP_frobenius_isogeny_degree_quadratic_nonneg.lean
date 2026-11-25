-- Prove2me | Theorems.Thm_DetDLP_frobenius_isogeny_degree_quadratic_nonneg
-- name    : DetDLP.frobenius_isogeny_degree_quadratic_nonneg
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T14:02:51.655154+00:00
-- url     : https://prove2.me/theorems/042ffed1-f5ce-4ec4-a14a-9635f642971b
-- title:
--   Nonnegativity of the Frobenius-Identity Endomorphism Degree Quadratic Form
-- statement:
--   For any prime $p > 3$ and elliptic curve $E / \mathbb{F}_p$ with point count $N = \#E(\mathbb{F}_p)$, the degree $\deg(m \phi_p - n \cdot \mathrm{id}_E)$ of the endomorphism $m \phi_p - n \cdot \mathrm{id}_E$ is given by the binary quadratic form $$Q(m, n) = m^2 p - m n (p + 1 - N) + n^2,$$ and satisfies $Q(m, n) \ge 0$ for all $(m, n) \in \mathbb{Z} \times \mathbb{Z}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1 (p. 11)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- Nonnegativity of the Frobenius-identity endomorphism degree quadratic form
`deg(m φ_p - n id_E) = m^2 p - m n (p + 1 - #E(F_p)) + n^2 ≥ 0` on `ℤ × ℤ`
for an elliptic curve `E / F_p` (`p > 3`). -/
theorem frobenius_isogeny_degree_quadratic_nonneg :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let N := Fintype.card E.toAffine.Point
        ∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * ((p : ℤ) + 1 - (N : ℤ)) + n ^ 2 := by
  sorry

end DetDLP
