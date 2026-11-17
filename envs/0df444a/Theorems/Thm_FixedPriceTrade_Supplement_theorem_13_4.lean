-- Prove2me | Theorems.Thm_FixedPriceTrade_Supplement_theorem_13_4
-- name    : FixedPriceTrade.Supplement.theorem_13_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:18:31.929013+00:00
-- url     : https://prove2.me/theorems/27978779-a3d1-4db8-be14-886bb0d1a418
-- title:
--   Theorem 13.4 — admissible bodies with a constant second-buyer body have $\mathcal R_2(Z,Y)\ge r_{\mathrm{fam}}$, with equality attained
-- statement:
--   Let $(Z,Y)$ be admissible bodies (independent bounded nonnegative vectors with $Z_1\ge Z_2$, $Y_1\le Y_2$ and $\Gamma_0(z)\le2$ for every price) whose second buyer's body $Z_2$ is almost surely constant. Then
--   $$
--   \mathcal R_2(Z,Y)\ \ge\ r_{\mathrm{fam}}=\inf_{\mathfrak F}R_f .
--   $$
--   The bound is attained: there are admissible bodies with an almost surely constant second buyer's body and $\mathcal R_2(Z,Y)=r_{\mathrm{fam}}$ (the bodies of the family minimizer of Proposition 13.2).
--
--   The theorem settles the conjecture $r^*_2=r_{\mathrm{fam}}$ on the class of normalized instances whose second buyer's body is a single value.
--
--   **Formalization Note** Bodies, $\Gamma_0$ and $\mathcal R_2$ are as in (57); $r_{\mathrm{fam}}$ is the infimum of $R_f$ over the family (63)–(65), not a numerical constant.
--
--   Differences from the source:
--   - encoding: independent bounded nonnegative vectors Z, Y → laws νZ, νY on ℝ² carried by a square [0,R]², joint law νZ.prod νY; reason: the joint law of independent vectors is the product
--   - encoding: Z₂ almost surely constant → ∃ c, νZ-a.e. z.2 = c; reason: definition
--   - reading: "The family minimizer of Proposition 13.2 has a constant second buyer’s body, so the bound is attained" → there exist admissible bodies with Z₂ a.s. constant and R₂(Z, Y) = r_fam; reason: Appendix D.5 (p.52): "the bodies of the family minimizer are admissible with R₂ = r_fam, so the bound is attained"
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), Theorem 13.4, p.30 (PDF p.30); (57), p.27; (63)–(65), p.29; proof Appendix D.5, pp.51–52

import Mathlib
import Definitions.Def_FixedPriceTrade_Supplement_R2
import Definitions.Def_FixedPriceTrade_Supplement_rFam

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set

/-- **Theorem 13.4 (the conjectured value for a constant second-buyer body)** — Lin, Shi, Dong, Li,
Yu, Zhang, *The Exact Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF
sha256 26832346…), p.30 (proof in Appendix D.5, pp.51–52).

1. If `(Z, Y)` are admissible bodies whose second buyer's body `Z₂` is almost surely constant,
   then `R₂(Z, Y) ≥ r_fam`.
2. The bound is attained: some admissible bodies with an almost surely constant `Z₂` have
   `R₂(Z, Y) = r_fam` (the bodies of the family minimizer of Proposition 13.2).

**Formalization Note.** Bodies, `Γ₀`, admissibility and `R₂` are as in (57) (`IsAdmissibleBodies`,
`R2`); `r_fam` is the infimum of `R_f` over the family (63)–(65) (`rFam`), not a numeral. -/
theorem theorem_13_4 :
    (∀ νZ νY : Measure (ℝ × ℝ), IsAdmissibleBodies νZ νY →
      (∃ c : ℝ, ∀ᵐ z ∂νZ, z.2 = c) → rFam ≤ R2 νZ νY) ∧
    (∃ νZ νY : Measure (ℝ × ℝ), IsAdmissibleBodies νZ νY ∧
      (∃ c : ℝ, ∀ᵐ z ∂νZ, z.2 = c) ∧ R2 νZ νY = rFam) := by sorry

end FixedPriceTrade.Supplement
