-- Prove2me | Theorems.Thm_FixedPriceTrade_Supplement_theorem_D
-- name    : FixedPriceTrade.Supplement.theorem_D
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:17:28.48993+00:00
-- url     : https://prove2.me/theorems/18a33e0b-8a67-4954-bedf-c02e70fd02fd
-- title:
--   Theorem D — two units are strictly harder: $r^*_2<0.7290804<0.738024<\beta_*$ and $r^*_{2,\mathrm{sym}}<0.83693$
-- statement:
--   In the two-unit model (buyer values $B_1\ge B_2>0$, seller costs $0<S_1\le S_2$, independent vectors with finite first moments, common price trading unit $i$ when $S_i\le z\le B_i$):
--
--   1. There are independent, finitely supported laws of strictly positive ordered buyer and seller vectors for which every common price $z$ has welfare ratio
--   $$
--   \frac{M_2+\Gamma_2(z)}{O_2}<0.7290804 .
--   $$
--   2. There is also a symmetric such instance ($(B_1,B_2)$ and $(S_2,S_1)$ identically distributed) in which every common price has ratio less than $0.83693$.
--   3. Consequently
--   $$
--   r^*_2<0.7290804<0.738024<\beta_*,\qquad r^*_{2,\mathrm{sym}}<0.83693,
--   $$
--   where $\beta_*=[C_*(2+\mathcal I(C_*))]^{-1}$ and $C_*\in(\tfrac14,\tfrac12)$ is the root of $C(2+\mathcal I(C))=1+\frac{C^2}{1-2C}e^{-\mathcal I(C)/2}$, with $\mathcal I$ in arctangent form as in Theorem A.
--
--   Together with Theorem A (the single-unit constant $\beta_*$) this shows that a common price guarantees strictly less welfare with two units than with one.
--
--   **Formalization Note** Instances are pairs of laws on $\mathbb R^2$ with the product as joint law; "every common price" is every real $z$. The instances are existential (the paper's 131-type data is in its supplementary material). The constant $\beta_*$ is written, for every root $C_*$ of (47) in $(\tfrac14,\tfrac12)$, exactly as in the published goal `FixedPriceTrade.theorem_A`, which also asserts that the root is unique.
--
--   Differences from the source:
--   - encoding: independent buyer and seller vectors, coordinates possibly dependent → a pair of laws νB, νS on ℝ² with joint law νB.prod νS; reason: the joint law of independent vectors is the product; every quantity depends only on it
--   - encoding: finitely supported laws → some finite set carries all the mass; reason: definition of finite support
--   - encoding: "every common price" → every real z; reason: for z ≤ 0 nothing trades (S₁ > 0), so the ratio is M₂/O₂, still covered
--   - encoding: β∗ = [C∗(2 + I(C∗))]⁻¹ for the unique root C∗ of (47) → for every root Cs ∈ (1/4,1/2) of (47) (arctangent form), 0.738024 < (Cs(2 + IArctan Cs))⁻¹; reason: same form as the published Theorem A, which proves existence and uniqueness of the root
--   - encoding: decimals 0.7290804, 0.738024, 0.83693 → rationals 7290804/10^7, 738024/10^6, 83693/10^5; reason: exact values of the printed decimals
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), Theorem D, p.26 (PDF p.26); model (56), p.26; proof Appendix E, p.53

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve
import Definitions.Def_FixedPriceTrade_Supplement_rStar2

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set Real

/-- **Theorem D (two units are strictly harder)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact
Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
p.26 (model (56), p.26).

1. There are independent, finitely supported laws of strictly positive ordered buyer and seller
   vectors for which every common price `z` has welfare ratio `(M₂ + Γ₂(z))/O₂ < 0.7290804`.
2. There is a symmetric such instance (`(B₁, B₂)` and `(S₂, S₁)` equal in law) with every common
   price at ratio `< 0.83693`.
3. `r∗₂ < 0.7290804 < 0.738024 < β∗` and `r∗_{2,sym} < 0.83693`, where `β∗ = [C∗(2 + I(C∗))]⁻¹`
   for the root `C∗ ∈ (1/4, 1/2)` of (47), written with the arctangent form of `I` exactly as in
   the published `FixedPriceTrade.theorem_A`.

**Formalization Note.** Instances are `IsTwoUnitInstance` (product of the two vector laws on `ℝ²`,
a.s. `B₁ ≥ B₂ > 0`, `0 < S₁ ≤ S₂`, finite first moments). "Every common price" is every real `z`.
The instances are existential: the 131-type data lives in the paper's supplementary material. -/
theorem theorem_D :
    (∃ νB νS : Measure (ℝ × ℝ), IsTwoUnitInstance νB νS ∧
      IsFinitelySupported νB ∧ IsFinitelySupported νS ∧
      ∀ z : ℝ, priceRatio2 νB νS z < (7290804 : ℝ) / 10 ^ 7) ∧
    (∃ νB νS : Measure (ℝ × ℝ), IsTwoUnitInstance νB νS ∧ IsSymmetricInstance νB νS ∧
      IsFinitelySupported νB ∧ IsFinitelySupported νS ∧
      ∀ z : ℝ, priceRatio2 νB νS z < (83693 : ℝ) / 10 ^ 5) ∧
    rStar2 < (7290804 : ℝ) / 10 ^ 7 ∧
    (7290804 : ℝ) / 10 ^ 7 < (738024 : ℝ) / 10 ^ 6 ∧
    (∀ Cs : ℝ, Cs ∈ Ioo (1 / 4 : ℝ) (1 / 2) →
      Cs * (2 + IArctan Cs) = 1 + Cs ^ 2 / (1 - 2 * Cs) * exp (-(IArctan Cs) / 2) →
      (738024 : ℝ) / 10 ^ 6 < (Cs * (2 + IArctan Cs))⁻¹) ∧
    rStar2Sym < (83693 : ℝ) / 10 ^ 5 := by sorry

end FixedPriceTrade.Supplement
