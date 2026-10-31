-- Prove2me | Theorems.Thm_CardinalMatching_lemma_15
-- name    : CardinalMatching.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:05.998507+00:00
-- url     : https://prove2.me/theorems/29776165-63f0-408e-9cb6-f8e3a9232dae
-- title:
--   Lemma 15: non-dummy agents get utility at most 1.6 and are not satiated (corrected: $n\ge 2$; $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   Suppose the original instance has $n\ge 2$ agents. For every non-dummy agent $i$ of $I'$,
--   $$
--   u'_i\cdot x_i\le 1.6 ,
--   $$
--   and in particular $i$ is not satiated: $u'_i\cdot x_i<u'_{ij}$ for some good $j$, i.e. $i$ does not receive one full unit of its most preferred goods.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$.
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
--   - correction: Lemma 15 for every n → hypothesis n ≥ 2; reason: for n = 1, I′ has k copies of the agent, k copies of the good, k awesome goods and k dummies; copies taking the awesome goods and dummies the good copies is EF and PO, yet each copy gets 2 > 1.6 (checked in Lean, Solutions/verification/CardinalMatching_C2.lean)
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 15, p.10

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

/-- **Lemma 15** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.10), corrected: "For any non-dummy agent i, ui · xi ≤ 1.6. In
particular i is not satiated." — for `n ≥ 2`.

"Not satiated" (p.7: "they are not getting 1 unit of their maximum utility goods") is stated as
`u_i · x_i < u_ij` for some good `j` of `I′`, i.e. `u_i · x_i` is below agent `i`'s maximal utility.

**Formalization Note (correction C2)** The printed lemma fails for `n = 1`: then `I′` has `k`
copies of the agent, `k` copies of the good, `k` awesome goods and `k` dummy agents; giving every
copy one awesome good and every dummy one copy of the good is envy-free and Pareto-optimal, yet
every copy gets utility `2 > 1.6`. The hypothesis `2 ≤ n` is added. -/
theorem lemma_15 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (hn : 2 ≤ n)
    (i : P.Agent) (hi : ¬ P.IsDummy i) :
    ∑ j, P.util i j * x i j ≤ 8 / 5 ∧ ∃ j, ∑ j', P.util i j' * x i j' < P.util i j := by sorry

end CardinalMatching
