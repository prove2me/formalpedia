-- Prove2me | Theorems.Thm_EllipsoidFitting_claim_6_6
-- name    : EllipsoidFitting.claim_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:01.671168+00:00
-- url     : https://prove2.me/theorems/dac4ca34-9b20-49c9-a90d-757258b6d692
-- title:
--   Claim 6.6 — coefficient mass shift $A_\delta=1+\Theta(\delta)$
-- statement:
--   Let $\tilde F_\delta(x)=\max(2x,\delta)$ and $A_\delta=C_\delta^2+\sum_{j\ge2}(b^{(\delta)}_j)^2$ its rescaled variance mass. There are constants $c,C,\delta_0>0$ such that for every $0<\delta<\delta_0$ the series $\sum_{j\ge2}(b_j^{(\delta)})^2$ converges and
--   $$
--   1+c\,\delta\le A_\delta\le1+C\,\delta .
--   $$
--
--   Since $A_F=1$ for the unperturbed $F$, replacing $F$ by the strictly positive $\tilde F_\delta$ moves the threshold $\gamma=1/(1+A_\delta)$ to $\tfrac12-\Theta(\delta)$; this is how the strictly positive definite fit of Theorem 1.1 is obtained.
--
--   **Formalization Note** The coefficients are $\mu_{\mathrm{sc}}$-integrals against $P_j$.
--
--   Differences from the source:
--   - reading: A_δ = 1 + Θ(δ) for sufficiently small δ > 0 → ∃ c, C, δ₀ > 0 with 1 + cδ ≤ A_δ ≤ 1 + Cδ for 0 < δ < δ₀; reason: Θ(δ) is two-sided with positive constants
--   - encoding: ∑_{j≥2} (b_j^{(δ)})² → tsum of the squares, with summability asserted; reason: a tsum of a non-summable family is 0 in Lean; summability holds by Bessel's inequality
--   - encoding: Chebyshev expansion coefficients of F̃_δ → ã_j = ∫ F̃_δ P_j dµsc; reason: the coefficients in the orthonormal basis {P_j} of Definition 2.1
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Claim 6.6, p.83 (PDF p.85)

import Mathlib
import Definitions.Def_EllipsoidFitting_massShift

set_option autoImplicit false

namespace EllipsoidFitting

/-- **Claim 6.6 (coefficient mass shift).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Claim 6.6, p.83:
"For sufficiently small δ > 0, Aδ = 1 + Θ(δ)."

There are constants `0 < c`, `0 < C` and `δ₀ > 0` such that for every `0 < δ < δ₀` the series
`∑_{j≥2} (b_j^{(δ)})²` converges and `1 + cδ ≤ A_δ ≤ 1 + Cδ`.

**Formalization Note** `Θ(δ)` is two-sided, so both bounds are asserted with positive constants.
`A_δ = C_δ² + ∑_{j≥2} (b_j^{(δ)})²` with the coefficients defined as `µsc`-integrals against
`P_j` (`Adelta`); summability is part of the conclusion so that the `tsum` is a genuine sum. -/
theorem claim_6_6 :
    ∃ c C δ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      Summable (fun j : ℕ => bdelta δ (j + 2) ^ 2) ∧
        1 + c * δ ≤ Adelta δ ∧ Adelta δ ≤ 1 + C * δ := by sorry

end EllipsoidFitting
