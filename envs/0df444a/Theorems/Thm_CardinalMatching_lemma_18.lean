-- Prove2me | Theorems.Thm_CardinalMatching_lemma_18
-- name    : CardinalMatching.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:44.592815+00:00
-- url     : https://prove2.me/theorems/93c531cd-b00f-4a72-a671-bf6bd3b9bed8
-- title:
--   Lemma 18: welfare weights of non-dummy agents are at most $5n^2$ (corrected: $n\ge 2$; $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   Suppose the original instance has $n\ge 2$ agents. After the rescaling, every non-dummy agent $i$ of $I'$ satisfies
--   $$
--   \alpha_i\le 5n^2 .
--   $$
--   Here $n$ is the number of agents of the original instance. The bound turns the envy-freeness argument of Lemma 19 into a quantitative one.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$. After Lemma 16 the data are rescaled so that the largest budget of a non-dummy agent is $1$ (`IsRescaled`).
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
--   - correction: Lemma 18 for every n → hypothesis n ≥ 2; reason: for n = 1 with the same allocation, α = 100 on the copies, awesome price 1, q = 199 on the copies is an optimal dual with copy budget 1 (so rescaled), yet α = 100 > 5 (checked in Lean, CardinalMatching_C2.lean)
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 18, p.10

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

/-- **Lemma 18** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.10), corrected: "For any non-dummy agent i we have αi ≤ 5n²." — for
`n ≥ 2`, after the rescaling that makes the maximum budget of a non-dummy agent exactly 1
(`IsRescaled`, p.10). Here `n` is the number of agents of the original instance.

**Formalization Note (correction)** The printed lemma fails for `n = 1`: with every copy holding
one awesome good, every positive `α` makes `x` `φ`-optimal; taking `α_i = 100` for the copies,
awesome price `1`, `q_i = 199` for the copies (and the dummies' part of the dual chosen
accordingly) gives an optimal dual with every copy's budget equal to `1`, yet `α_i = 100 > 5`.
The hypothesis `2 ≤ n` is added (as for Lemma 15, on which the proof rests). -/
theorem lemma_18 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q)
    (hR : P.IsRescaled x α q) (hn : 2 ≤ n) (i : P.Agent) (hi : ¬ P.IsDummy i) :
    α i ≤ 5 * (n : ℝ) ^ 2 := by sorry

end CardinalMatching
