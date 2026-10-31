-- Prove2me | Theorems.Thm_CardinalMatching_theorem_24
-- name    : CardinalMatching.theorem_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:18.157309+00:00
-- url     : https://prove2.me/theorems/814ef9f1-e889-4d8d-be43-fdfacf62f32e
-- title:
--   Theorem 24: the contraction is a $3/n$-approximate HZ equilibrium (corrected: $\hat x$ normalized by $1/k$; $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   If $\varepsilon\le \dfrac{1}{5n^5}$, then the contraction $(\hat x,\hat p)$ of the rescaled Step 2 data, with
--   $$
--   \hat x_{ij}=\frac1k\sum_{c,c'}x_{(i,c),(j,c')},\qquad \hat p_j=\text{the common price of the copies of } j,
--   $$
--   is a $\tfrac3n$-approximate HZ equilibrium (Definition 10) of the original instance $I$ with utilities $u$.
--
--   This is the correctness of the reduction of Theorem 8: from any EF+PO allocation of $I'$ one reads off an approximate HZ equilibrium of $I$.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$. After Lemma 16 the data are rescaled so that the largest budget of a non-dummy agent is $1$ (`IsRescaled`).
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
--   - correction: x̂_ij = "the average over all x_i′j′" over the k² copy pairs (Step 5) → x̂_ij = (1/k)·Σ over the k² copy pairs; reason: the literal average makes every row sum ≤ 1/k; for n = 4 and any admissible k ≥ 2 this violates ∑_j x̂_ij ≥ 1 − 3/n = 1/4, so Theorem 24 would be false; the proof's ∑_j x̂_ij ∈ [1 − 1/n, 1] needs 1/k
--   - reading: p̂ is not defined in the paper → p̂_j = average price of the k copies of j; reason: by Lemma 14 all copies have one price; the proof's "no agent overspends" refers to it
--   - reading: max { u_i · y | Σ_j y_j = 1, p · y ≤ 1 } in Definition 10 (the set can be empty) → IsApproxHZ asserts that this maximum exists (at least one bundle is feasible) and compares with it; reason: max ∅ is undefined; without this clause p_j = 1/(1 − ε), x_ij = (1 − ε)/n would be an answer on every instance
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Theorem 24, p.14 (Step 5, p.14)

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context
import Definitions.Def_CardinalMatching_ModParams_xhat
import Definitions.Def_CardinalMatching_IsApproxHZ

namespace CardinalMatching

/-- **Theorem 24** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.14): "If ǫ ≤ 1/(5n⁵), then (x̂, p̂) is a 3/n-approximate HZ equilibrium
in the original instance I."

`x̂` and `p̂` are the contraction of Step 5 (`xhat`, `phat`) of the rescaled Step-2 data
(`IsStep2Context`, `IsRescaled`); "approximate HZ equilibrium" is Definition 10 (pp.6–7) for the
original utilities `u`.

**Formalization Note** `x̂_ij = (1/k) ∑ x_{i′j′}` over the copy pairs (the printed "average" over
the `k²` pairs is corrected, see `xhat`); `p̂_j` is the common price of the copies of `j`
(`phat`). -/
theorem theorem_24 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q)
    (hR : P.IsRescaled x α q) (hε : P.ε ≤ 1 / (5 * (n : ℝ) ^ 5)) :
    IsApproxHZ P.u (3 / (n : ℝ)) (P.xhat x) (P.phat p) := by sorry

end CardinalMatching
