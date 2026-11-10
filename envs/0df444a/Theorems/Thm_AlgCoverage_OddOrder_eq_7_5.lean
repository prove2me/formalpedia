-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_7_5
-- name    : AlgCoverage.OddOrder.eq_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:47:46.2642+00:00
-- url     : https://prove2.me/theorems/fdf5dc71-7dd1-4f06-94fd-1ae0d44fbb2d
-- title:
--   §7, Eq. (7.5) — averaged good-mass deficit $\mathbb E_U[1-\gamma(U_S)]\le\beta=\min\{1,JA_*(2^{-\ell_1}+2^{-\ell_2})\}$
-- statement:
--   Let $G$ be a finite group of odd order with a supplied series (6.1) having $J$ layers and maximal layer dimension $D$. Let $T\ge3$, an arity $j\le T$, and suffix block lengths $\ell_1,\ell_2\ge1$ with $\ell_1+\ell_2\le k$. Averaging over uniform raw masks $U\in(\{0,1\}^k)^j$ (empty and repeated rows allowed),
--   $$\mathbb E_U\big[1-\gamma(U_S)\big]\le\beta:=\min\{1,\ JA_*(2^{-\ell_1}+2^{-\ell_2})\}, \tag{7.5}$$
--   where $A_*$ is the envelope selected in (5.9): $A_*=A(T,D)$ for the general matrix route (every series), and $A_*=A_{\rm sc}(T)$ for the prime-order route (every layer of dimension one, the series (5.8)). Both choices are asserted.
--
--   Differences from the source:
--   - encoding: a supplied G-normal elementary-abelian series (6.1) and FULL as surjectivity of the coefficient map at every layer → s : NormalEASeries G (0-based layers A (r+1)/A r, every layer nontrivial: d_r ≥ 1) and FULL s x U: every target in A_{r+1}^j is hit modulo A_r by the layer word ∏ P_i a_i P_i⁻¹ for some lifts a ∈ A_{r+1}^k; reason: the layer quotient is abelian and normal in G/A_r, so this is surjectivity of the induced linear coefficient map with coefficients θ(prefix) of form (5.1); d_r ≥ 1 is the reading of (6.1) declared in eq_6_1 (J ≤ log₃ N needs it), and a series with trivial layers collapses to one without them with the same FULL and no larger J
--   - encoding: a contiguous suffix S split into two successive nonempty blocks S₁, S₂ → S₁ = positions k−ℓ₁−ℓ₂, …, k−ℓ₂−1 and S₂ = positions k−ℓ₂, …, k−1 (0-based), ℓ₁, ℓ₂ ≥ 1, ℓ₁ + ℓ₂ ≤ k; reason: every split of a suffix into two successive nonempty blocks has this form; (8.2) names their lengths ℓ₁, ℓ₂
--   - encoding: local FULL of a block (the block restarted at the identity) and γ(U_S) = (1 − δ₁ − δ₂)₊ with 1 − δ_a the mass of the block subprobability μ_a → localFULL = FULL of the rows with their bits outside the block set to 0; gammaS = max 0 (1 − Pr(local test 1 fails) − Pr(local test 2 fails)) over iid inputs; reason: for a position i in a contiguous block the selected prefix inside the block is exactly the block-local prefix; the mass of μ_a is the probability that its local test passes, and it depends only on the block inputs
--   - encoding: E_U, averaged first over masks with the quotient stream fixed and then over inputs → the average over all 2^{jk} raw mask arrays of 1 − gammaS (gammaS already integrates the inputs); reason: both orders give the same finite double sum
--   - reading: 'the selected rank bound in (5.9)', arities at most T → both envelope choices: A(T, D) for every series and A_sc(T) when every layer has dimension one, for every j ≤ T with T ≥ 3; reason: (5.9) selects the envelope by the route; the paper uses both
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 23 (PDF 24), §7, Eq. (7.5); p. 20 (PDF 21), Eq. (5.9)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_CommonStream
import Definitions.Def_AlgCoverage_OddOrder_Series
import Definitions.Def_AlgCoverage_OddOrder_TwoBlock

namespace AlgCoverage.OddOrder

/-- §7, Eq. (7.5), Lin, printed p. 23 / PDF 24. `G` of odd order with a supplied series (`J` layers,
`D = max d_r`), suffix blocks of lengths `ℓ₁, ℓ₂ ≥ 1` (`ℓ₁ + ℓ₂ ≤ k`), arity `j ≤ T`, `T ≥ 3`. Averaged
over uniform raw masks `U ∈ ({0,1}^k)^j`: `E_U[1 − γ(U_S)] ≤ β = min{1, J A_*(2^{−ℓ₁} + 2^{−ℓ₂})}`, for
the general envelope `A_* = A(T, D)` and, when every layer has dimension one (the series (5.8)), for
the scalar envelope `A_* = A_sc(T)` (the selection (5.9)). -/
theorem eq_7_5 (G : Type*) [Group G] [Fintype G] (hodd : Odd (Fintype.card G))
    (s : NormalEASeries G) (T j k ℓ₁ ℓ₂ : ℕ) (hT : 3 ≤ T) (hj : j ≤ T)
    (h₁ : 1 ≤ ℓ₁) (h₂ : 1 ≤ ℓ₂) (hk : ℓ₁ + ℓ₂ ≤ k) :
    (∑ U : Fin j → Fin k → Bool, (1 - gammaS s k ℓ₁ ℓ₂ U)) / (2 : ℝ) ^ (j * k) ≤
        betaDef s.J (envA T s.D) ℓ₁ ℓ₂ ∧
    ((∀ r, r < s.J → s.d r = 1) →
      (∑ U : Fin j → Fin k → Bool, (1 - gammaS s k ℓ₁ ℓ₂ U)) / (2 : ℝ) ^ (j * k) ≤
        betaDef s.J (envAsc T) ℓ₁ ℓ₂) := by sorry

end AlgCoverage.OddOrder
