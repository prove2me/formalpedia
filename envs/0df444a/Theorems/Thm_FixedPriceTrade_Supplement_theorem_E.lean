-- Prove2me | Theorems.Thm_FixedPriceTrade_Supplement_theorem_E
-- name    : FixedPriceTrade.Supplement.theorem_E
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:18:03.200832+00:00
-- url     : https://prove2.me/theorems/40b01b54-fa6e-4c8c-a568-b11b72c45227
-- title:
--   Theorem E — pricing for ordered buyer pairs: the contraction $\mathcal T_{d,\vartheta}$, the functional $\mathcal J^{(2)}_d$ and the budget criterion $\beta\mathcal J^{(2)}_d\le1$
-- statement:
--   For every ordered buyer pair $Z_1\ge_{\mathrm{st}}Z_2$ supported on $[0,\bar b]$ and every $d>0$:
--
--   1. **(i)** For each compensation $\vartheta\in\mathcal V$, the operator $\mathcal T_{d,\vartheta}$ of (60) has a bounded fixed point $\varpi_{d,\vartheta}$ on $[0,\bar b]$; it is the only bounded Borel fixed point, it is feasible, and it is pointwise below every feasible cumulative mass. For bounded Borel $\varpi,\varpi'$,
--   $$
--   \sup_{[0,\bar b]}|\mathcal T_{d,\vartheta}\varpi-\mathcal T_{d,\vartheta}\varpi'|\le\frac{\bar b}{1+\bar b}\sup_{[0,\bar b]}|\varpi-\varpi'|,
--   $$
--   and the iterates $\mathcal T_{d,\vartheta}^n0$ converge uniformly on $[0,\bar b]$ to $\varpi_{d,\vartheta}$.
--   2. **(ii)** $\varpi_{d,\vartheta}(0)$ is jointly convex in $(d,\vartheta)\in(0,\infty)\times\mathcal V$, and the minimum $\mathcal J^{(2)}_d(H_1,H_2)=\min_{\vartheta\in\mathcal V}\varpi_{d,\vartheta}(0)$ is attained.
--   3. **(iii)** For $0<\beta<1$, there is a price probability with bounded support satisfying
--   $$
--   \sum_{i=1}^2\int g_i(s_i,z)\,\pi(dz)\ge\beta\sum_{i=1}^2\bar L_i(s_i)-\beta d(s_1+s_2)\qquad(0\le s_1\le s_2)\tag{62}
--   $$
--   if and only if $\beta\mathcal J^{(2)}_d(H_1,H_2)\le1$. At $d=(1-\beta)/\beta$ every such price is a welfare guarantee of $\beta$ in the normalized model: for every bounded nonnegative seller body $Y_1\le Y_2$ independent of the buyers,
--   $$
--   \mathbb E(Y_1+Y_2)+\int\Gamma_0\,d\pi\ \ge\ \beta\Big[2+\sum_{i=1}^2\mathbb E\max\{Z_i,Y_i\}\Big].
--   $$
--   4. **(iv)** If $H_i^\delta$ is the survival function of $\delta\lfloor Z_i/\delta\rfloor$ ($\delta>0$), then $\mathcal J^{(2)}_d(H_1,H_2)\le\mathcal J^{(2)}_d(H_1^\delta,H_2^\delta)+\delta$. Consequently the supremum of $\mathcal J^{(2)}_d$ over bounded ordered buyer bodies equals the supremum over finitely supported ordered buyer bodies.
--
--   This is the two-unit pricing step: for fixed buyers it reduces the existence of a price meeting a welfare target against every ordered seller pair to a one-number budget condition, and part (iv) lets the worst case be searched over finite supports.
--
--   **Formalization Note** The buyer pair is given by its marginal laws. The contraction is stated as: if $|\varpi-\varpi'|\le c$ on $[0,\bar b]$ then $|\mathcal T\varpi-\mathcal T\varpi'|\le\frac{\bar b}{1+\bar b}c$ on $[0,\bar b]$. The rounded bodies are computed on the same $[0,\bar b]$. The suprema in (iv) are taken in the extended reals over all $(\mu_1,\mu_2,\bar b)$.
--
--   Differences from the source:
--   - encoding: buyer bodies Z₁ ≥st Z₂ with survival functions H₁ ≥ H₂, J^(2)_d(H₁, H₂) → marginal laws μ₁, μ₂ on [0, b̄] with μ₂(s,∞) ≤ μ₁(s,∞) for all s; J2 μ₁ μ₂ b̄ d; reason: a law on ℝ is determined by its survival function; only marginals enter
--   - encoding: ϖ_{d,ϑ}, the unique bounded fixed point of T_{d,ϑ} → fixedMass, the pointwise infimum of feasible masses, with (i) asserting it is the fixed point; reason: the paper proves these coincide; (i) states it
--   - reading: "T_{d,ϑ} has a unique bounded fixed point" → unique among bounded Borel functions on [0, b̄]; reason: T_{d,ϑ} is defined on bounded Borel functions (p.28)
--   - reading: "contraction factor b̄/(1 + b̄)" → |ϖ − ϖ′| ≤ c on [0, b̄] implies |Tϖ − Tϖ′| ≤ (b̄/(1+b̄))·c on [0, b̄], for bounded Borel ϖ, ϖ′; reason: the uniform-norm contraction the proof (B.4) establishes
--   - generalization: "the pointwise least feasible cumulative mass" (cumulative masses are right-continuous, p.28) → below every nonnegative, nonincreasing, bounded ϖ with ψ₁ ≥ −ϑ and ψ₂ ≥ ϑ on [0, b̄], right-continuous or not; reason: a larger competitor class; it contains the right-continuous masses, and the B.4 induction does not use right-continuity
--   - encoding: "price probability with bounded support" → probability measure π with π(−∞,0) = 0 and π(R,∞) = 0 for some R; reason: prices are nonnegative; unused mass sits at zero
--   - generalization: welfare guarantee "against every ordered seller distribution in the normalized model" (buyer bodies Z with Z₁ ≥ Z₂) → for every law νZ on ℝ² with marginals μ₁, μ₂ (any coupling) and every bounded nonnegative seller body law νY with Y₁ ≤ Y₂ a.s., independent (product); reason: both sides depend only on the buyer marginals, so every coupling (including the ordered one) is covered
--   - encoding: J^(2)_d does not depend on b̄; suprema over bounded ordered buyer bodies → b̄ an explicit argument of J2; suprema in EReal over all (μ₁, μ₂, b̄); reason: independence of b̄ is a result of B.4, not a definition; EReal avoids the default value of sSup on unbounded sets
--   - encoding: H_i^δ, the survival function of δ⌊Z_i/δ⌋ → the image of μᵢ under x ↦ δ⌊x/δ⌋, on the same b̄; reason: the law of δ⌊Zᵢ/δ⌋; the rounded bodies stay in [0, b̄]
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), Theorem E, p.28 (PDF p.28); definitions (58)–(60), pp.27–28; proof Appendix B.4, pp.41–43

import Mathlib
import Definitions.Def_FixedPriceTrade_Supplement_R2
import Definitions.Def_FixedPriceTrade_Supplement_J2

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set Filter

/-- **Theorem E (pricing for ordered buyer pairs)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact
Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
p.28 (definitions (58)–(60), pp.27–28; proof Appendix B.4).

For every ordered buyer pair `Z₁ ≥_st Z₂` supported on `[0, b̄]` and every `d > 0`:

(i) for each `ϑ ∈ V`, `ϖ_{d,ϑ}` is a bounded fixed point of `T_{d,ϑ}` on `[0, b̄]`, the only bounded
    Borel one, and the pointwise least feasible cumulative mass (itself feasible); `T_{d,ϑ}` is a
    contraction with factor `b̄/(1 + b̄)` in the uniform distance on `[0, b̄]`, and the iterates from
    zero converge uniformly on `[0, b̄]` to `ϖ_{d,ϑ}`;
(ii) `ϖ_{d,ϑ}(0)` is jointly convex in `(d, ϑ) ∈ (0, ∞) × V`, and the minimum
    `J^{(2)}_d = min_{ϑ ∈ V} ϖ_{d,ϑ}(0)` is attained;
(iii) for `0 < β < 1`, a price probability with bounded support satisfying (62) exists iff
    `β J^{(2)}_d ≤ 1`; at `d = (1 − β)/β` every such price gives
    `E(Y₁ + Y₂) + ∫ Γ₀ dπ ≥ β[2 + Σᵢ E max{Zᵢ, Yᵢ}]` against every ordered seller body `Y`
    independent of the buyers;
(iv) for every `δ > 0`, `J^{(2)}_d(H₁, H₂) ≤ J^{(2)}_d(H₁^δ, H₂^δ) + δ`, where `H_i^δ` is the
    survival function of `δ⌊Zᵢ/δ⌋`; and the supremum of `J^{(2)}_d` over bounded ordered buyer
    bodies equals the supremum over finitely supported ones.

**Formalization Note.** The buyer pair is given by its marginals `μ₁, μ₂` (only they enter);
the rounded pair is the image of `μᵢ` under `x ↦ δ⌊x/δ⌋`, computed on the same `[0, b̄]`. In the
welfare clause the buyer body vector is any law on `ℝ²` with marginals `μ₁, μ₂`. The suprema in
(iv) are taken in `EReal`, over all `(μ₁, μ₂, b̄)`, because `J^{(2)}_d ≤ 1 + b̄` is not uniform in
`b̄`. -/
theorem theorem_E :
    (∀ μ1 μ2 : Measure ℝ, ∀ b : ℝ, IsBuyerPair μ1 μ2 b → ∀ d : ℝ, 0 < d →
      -- (i)
      (∀ ϑ : ℝ → ℝ, IsCompensation b ϑ →
        (∀ s ∈ Icc 0 b, Tmass μ1 μ2 b d ϑ (fixedMass μ1 μ2 b d ϑ) s = fixedMass μ1 μ2 b d ϑ s) ∧
        BddAbove (fixedMass μ1 μ2 b d ϑ '' Icc 0 b) ∧
        BddBelow (fixedMass μ1 μ2 b d ϑ '' Icc 0 b) ∧
        (∀ ϖ : ℝ → ℝ, Measurable ϖ → BddAbove (ϖ '' Icc 0 b) → BddBelow (ϖ '' Icc 0 b) →
          (∀ s ∈ Icc 0 b, Tmass μ1 μ2 b d ϑ ϖ s = ϖ s) →
          EqOn ϖ (fixedMass μ1 μ2 b d ϑ) (Icc 0 b)) ∧
        IsFeasibleMass μ1 μ2 b d ϑ (fixedMass μ1 μ2 b d ϑ) ∧
        (∀ ϖ : ℝ → ℝ, IsFeasibleMass μ1 μ2 b d ϑ ϖ →
          ∀ s ∈ Icc 0 b, fixedMass μ1 μ2 b d ϑ s ≤ ϖ s) ∧
        (∀ ϖ ϖ' : ℝ → ℝ, Measurable ϖ → Measurable ϖ' →
          BddAbove (ϖ '' Icc 0 b) → BddBelow (ϖ '' Icc 0 b) →
          BddAbove (ϖ' '' Icc 0 b) → BddBelow (ϖ' '' Icc 0 b) →
          ∀ c : ℝ, (∀ t ∈ Icc 0 b, |ϖ t - ϖ' t| ≤ c) →
          ∀ s ∈ Icc 0 b, |Tmass μ1 μ2 b d ϑ ϖ s - Tmass μ1 μ2 b d ϑ ϖ' s| ≤ b / (1 + b) * c) ∧
        TendstoUniformlyOn (fun n : ℕ => (Tmass μ1 μ2 b d ϑ)^[n] 0)
          (fixedMass μ1 μ2 b d ϑ) atTop (Icc 0 b)) ∧
      -- (ii), attainment
      (∃ ϑ : ℝ → ℝ, IsCompensation b ϑ ∧ fixedMass μ1 μ2 b d ϑ 0 = J2 μ1 μ2 b d) ∧
      (∀ ϑ : ℝ → ℝ, IsCompensation b ϑ → J2 μ1 μ2 b d ≤ fixedMass μ1 μ2 b d ϑ 0) ∧
      -- (iii), the equivalence
      (∀ β ∈ Ioo (0 : ℝ) 1,
        (∃ π : Measure ℝ, IsPriceProb π ∧ Satisfies62 μ1 μ2 β d π) ↔ β * J2 μ1 μ2 b d ≤ 1) ∧
      -- (iv), rounding
      (∀ δ : ℝ, 0 < δ →
        J2 μ1 μ2 b d ≤
          J2 (μ1.map (fun x : ℝ => δ * (⌊x / δ⌋ : ℝ))) (μ2.map (fun x : ℝ => δ * (⌊x / δ⌋ : ℝ)))
            b d + δ)) ∧
    -- (ii), joint convexity in (d, ϑ)
    (∀ μ1 μ2 : Measure ℝ, ∀ b : ℝ, IsBuyerPair μ1 μ2 b →
      ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ → ∀ ϑ₁ ϑ₂ : ℝ → ℝ, IsCompensation b ϑ₁ → IsCompensation b ϑ₂ →
      ∀ a ∈ Icc (0 : ℝ) 1,
        fixedMass μ1 μ2 b (a * d₁ + (1 - a) * d₂) (a • ϑ₁ + (1 - a) • ϑ₂) 0 ≤
          a * fixedMass μ1 μ2 b d₁ ϑ₁ 0 + (1 - a) * fixedMass μ1 μ2 b d₂ ϑ₂ 0) ∧
    -- (iii), the welfare guarantee at d = (1 - β)/β
    (∀ μ1 μ2 : Measure ℝ, ∀ b : ℝ, IsBuyerPair μ1 μ2 b → ∀ β ∈ Ioo (0 : ℝ) 1,
      ∀ π : Measure ℝ, IsPriceProb π → Satisfies62 μ1 μ2 β ((1 - β) / β) π →
      ∀ νZ νY : Measure (ℝ × ℝ), νZ.map Prod.fst = μ1 → νZ.map Prod.snd = μ2 → IsSellerBody νY →
        β * (2 + ∫ x, max x.1.1 x.2.1 + max x.1.2 x.2.2 ∂(νZ.prod νY)) ≤
          (∫ y, y.1 + y.2 ∂νY) + ∫ z, Gamma0 νZ νY z ∂π) ∧
    -- (iv), the two suprema agree
    (∀ d : ℝ, 0 < d →
      sSup {x : EReal | ∃ μ1 μ2 : Measure ℝ, ∃ b : ℝ, IsBuyerPair μ1 μ2 b ∧
          x = ((J2 μ1 μ2 b d : ℝ) : EReal)} =
        sSup {x : EReal | ∃ μ1 μ2 : Measure ℝ, ∃ b : ℝ, IsBuyerPair μ1 μ2 b ∧
          (∃ t : Set ℝ, t.Finite ∧ μ1 tᶜ = 0) ∧ (∃ t : Set ℝ, t.Finite ∧ μ2 tᶜ = 0) ∧
          x = ((J2 μ1 μ2 b d : ℝ) : EReal)}) := by sorry

end FixedPriceTrade.Supplement
