-- Prove2me | Theorems.Thm_DPVerify_constants_display
-- name    : DPVerify.constants_display
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T07:52:26.60176+00:00
-- url     : https://prove2.me/theorems/1194ac06-ee19-4dca-a776-9608bbc8a2f2
-- title:
--   Proof of Theorem 4.1, pp.14–15 — with $\alpha=0.001$, $\rho\le10^{-4}$, $t=6$, $\kappa=20$: completeness $\ge0.733$, soundness $\le0.0943$
-- statement:
--   Let $\alpha=0.001$, $t=6$, $\kappa=20$ and $\rho\le10^{-4}$. Then the completeness bound of Theorem 4.1's proof satisfies
--
--   $$
--   \Bigl(1-\frac1t-t(\alpha+\rho)\Bigr)\frac{\kappa^2}{\kappa^2+t^2}-4\kappa\rho\pi\;\ge\;0.733,
--   $$
--
--   and the soundness bound satisfies
--
--   $$
--   \pi\kappa(\alpha+\rho)+4\kappa\pi\rho\;\le\;0.0943 .
--   $$
--
--   These are the concrete constants $0.733$ and $0.0943$ stated in Theorem 4.1 and used by Corollary 4.5.
--
--   Differences from the source:
--   - encoding: $\Pr[\text{accept}\mid\text{yes}]\ge0.733$, $\Pr[\text{accept}\mid\text{no}]\le0.0943$ → the two bound expressions of pp.14–15 that the page evaluates; reason: the display is the arithmetic on these expressions
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.14 (PDF p.17) and p.15 (PDF p.18)

import Mathlib

set_option autoImplicit false

namespace DPVerify

/-- §4, proof of Theorem 4.1, the constants display (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), pp.14–15 = PDF pp.17–18): with
`α = 0.001`, `ρ ≤ 10⁻⁴`, `t = 6` and `κ = 20`, the completeness bound
`(1 − 1/t − t(α + ρ)) (κ² / (κ² + t²)) − 4κρπ` (p.14) is at least `0.733` and the soundness bound
`πκ(α + ρ) + 4κπρ` (p.15) is at most `0.0943`.

**Formalization Note** The probabilities `Pr[accept | yes]` and `Pr[accept | no]` are represented
by the two bound expressions of pp.14–15 that the page evaluates. -/
theorem constants_display (α t κ ρ : ℝ) (hα : α = 0.001) (ht : t = 6) (hκ : κ = 20)
    (hρ : ρ ≤ 1 / 10 ^ 4) :
    0.733 ≤ (1 - 1 / t - t * (α + ρ)) * (κ ^ 2 / (κ ^ 2 + t ^ 2)) - 4 * κ * ρ * Real.pi ∧
    Real.pi * κ * (α + ρ) + 4 * κ * Real.pi * ρ ≤ 0.0943 := by sorry

end DPVerify
