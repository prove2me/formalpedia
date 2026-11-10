-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_7_3_7_4
-- name    : AlgCoverage.OddOrder.eq_7_3_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:47:31.032478+00:00
-- url     : https://prove2.me/theorems/3de79987-ca21-4d1f-b7f5-6ce806ecfd56
-- title:
--   §7, Eqs. (7.3)–(7.4) — two-block LOWER/UPPER sandwich with outside-measurable weights, and the unweighted COMPLEMENT bound
-- statement:
--   Let $G$ be a finite group of odd order $N$ with a supplied series (6.1), $X\in G^k$ iid uniform inputs, a suffix $S$ split into successive nonempty blocks $S_1,S_2$ of lengths $\ell_1,\ell_2$, fixed masks $U=(v_1,\dots,v_j)$ and a fixed target $z\in G^j$. Let $E_S$ be the event that both local FULL tests pass and $\gamma(U_S)$ the good mass of §7. Then for every nonnegative weight $Z$ that is measurable with respect to the inputs outside $S$,
--   $$\gamma(U_S)\,\mathbb E_XZ\le N^j\,\mathbb E_X\big[\mathbf 1\{W_U=z,E_S\}Z\big]\le\mathbb E_XZ \tag{7.3}$$
--   (the LOWER and the good UPPER interfaces); the good event implies global FULL, $E_S\subseteq\mathrm{FULL}(U)$; and, unweighted and under the same fixed-mask full-input measure,
--   $$0\le N^j\Pr_X\big(W_U=z,\ \mathrm{FULL}(U),\ E_S^c\big)\le1-\gamma(U_S). \tag{7.4}$$
--   Here $W_U=z$ means $W_{v_a}=z_a$ for every row $a$. (The paper shows on p. 23 that an outside-weighted version of (7.4) is false.)
--
--   Differences from the source:
--   - encoding: a supplied G-normal elementary-abelian series (6.1) and FULL as surjectivity of the coefficient map at every layer → s : NormalEASeries G (0-based layers A (r+1)/A r, every layer nontrivial: d_r ≥ 1) and FULL s x U: every target in A_{r+1}^j is hit modulo A_r by the layer word ∏ P_i a_i P_i⁻¹ for some lifts a ∈ A_{r+1}^k; reason: the layer quotient is abelian and normal in G/A_r, so this is surjectivity of the induced linear coefficient map with coefficients θ(prefix) of form (5.1); d_r ≥ 1 is the reading of (6.1) declared in eq_6_1 (J ≤ log₃ N needs it), and a series with trivial layers collapses to one without them with the same FULL and no larger J
--   - encoding: a contiguous suffix S split into two successive nonempty blocks S₁, S₂ → S₁ = positions k−ℓ₁−ℓ₂, …, k−ℓ₂−1 and S₂ = positions k−ℓ₂, …, k−1 (0-based), ℓ₁, ℓ₂ ≥ 1, ℓ₁ + ℓ₂ ≤ k; reason: every split of a suffix into two successive nonempty blocks has this form; (8.2) names their lengths ℓ₁, ℓ₂
--   - encoding: local FULL of a block (the block restarted at the identity) and γ(U_S) = (1 − δ₁ − δ₂)₊ with 1 − δ_a the mass of the block subprobability μ_a → localFULL = FULL of the rows with their bits outside the block set to 0; gammaS = max 0 (1 − Pr(local test 1 fails) − Pr(local test 2 fails)) over iid inputs; reason: for a position i in a contiguous block the selected prefix inside the block is exactly the block-local prefix; the mass of μ_a is the probability that its local test passes, and it depends only on the block inputs
--   - encoding: nonnegative integrable F_{S^c}-measurable weight Z → Z : G^k → ℝ, Z ≥ 0, with Z x = Z x' whenever x and x' agree outside S; reason: on a finite product space measurability with respect to the outside coordinates is exactly this, and integrability is automatic
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 22 (PDF 23), §7, Eqs. (7.3)–(7.4)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Series
import Definitions.Def_AlgCoverage_OddOrder_TwoBlock

namespace AlgCoverage.OddOrder

/-- §7, Eqs. (7.3)–(7.4), Lin, printed p. 22 / PDF 23. `G` of odd order `N` with a supplied series;
`k` iid uniform inputs; the suffix `S` of length `ℓ₁ + ℓ₂ ≤ k` split into successive nonempty blocks
`S₁` (length `ℓ₁`) and `S₂` (length `ℓ₂`); fixed masks `U` (`j` rows) and target `z ∈ G^j`.
(7.3) LOWER/UPPER: for every nonnegative weight `Z` depending only on the inputs outside `S`,
`γ(U_S) E Z ≤ N^j E[1{W_U = z, E_S} Z] ≤ E Z`; the good event `E_S` implies global FULL;
(7.4) COMPLEMENT: `0 ≤ N^j Pr(W_U = z, FULL(U), E_Sᶜ) ≤ 1 − γ(U_S)`. -/
theorem eq_7_3_7_4 (G : Type*) [Group G] [Fintype G] (hodd : Odd (Fintype.card G))
    (s : NormalEASeries G) (j k ℓ₁ ℓ₂ : ℕ) (h₁ : 1 ≤ ℓ₁) (h₂ : 1 ≤ ℓ₂) (hk : ℓ₁ + ℓ₂ ≤ k)
    (U : Fin j → Fin k → Bool) (z : Fin j → G) :
    (∀ Z : (Fin k → G) → ℝ, (∀ x, 0 ≤ Z x) →
      (∀ x x' : Fin k → G, (∀ i, inSuffix k ℓ₁ ℓ₂ i = false → x i = x' i) → Z x = Z x') →
      gammaS s k ℓ₁ ℓ₂ U * expIid G k Z ≤
          (Fintype.card G : ℝ) ^ j * expIid G k
            (Set.indicator {x | (∀ a, word x (U a) = z a) ∧ GoodS s ℓ₁ ℓ₂ x U} Z) ∧
        (Fintype.card G : ℝ) ^ j * expIid G k
            (Set.indicator {x | (∀ a, word x (U a) = z a) ∧ GoodS s ℓ₁ ℓ₂ x U} Z) ≤
          expIid G k Z) ∧
    (∀ x : Fin k → G, GoodS s ℓ₁ ℓ₂ x U → FULL s x U) ∧
    (0 ≤ (Fintype.card G : ℝ) ^ j *
        probIid G k (fun x => (∀ a, word x (U a) = z a) ∧ FULL s x U ∧ ¬ GoodS s ℓ₁ ℓ₂ x U) ∧
      (Fintype.card G : ℝ) ^ j *
          probIid G k (fun x => (∀ a, word x (U a) = z a) ∧ FULL s x U ∧ ¬ GoodS s ℓ₁ ℓ₂ x U) ≤
        1 - gammaS s k ℓ₁ ℓ₂ U) := by sorry

end AlgCoverage.OddOrder
