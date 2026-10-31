-- Prove2me | Theorems.Thm_CardinalMatching_lemma_16
-- name    : CardinalMatching.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:54.162985+00:00
-- url     : https://prove2.me/theorems/a6dc1521-ef64-4eae-bcc9-50f8fe67d08d
-- title:
--   Lemma 16: some non-dummy agent has a positive budget (corrected: $n\ge 2$; $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   Suppose the original instance has $n\ge 2$ agents. Then there is a non-dummy agent $i$ of $I'$ with
--   $$
--   b_i>0 .
--   $$
--   This allows the rescaling after which the largest budget of a non-dummy agent is $1$.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$.
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
--   - correction: Lemma 16 for every n → hypothesis n ≥ 2; reason: for n = 1 with the same allocation, α = 1, p = 0, q_i = max_j α_i u′_ij is an optimal dual and every budget is 0 (checked in Lean, CardinalMatching_C2.lean)
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 16, p.10

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

/-- **Lemma 16** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.10), corrected: "There exists at least one non-dummy agent i with
bi > 0." — for `n ≥ 2`. Running context of Step 2 (`IsStep2Context`).

**Formalization Note (correction)** The printed lemma fails for `n = 1`: with every copy of the
agent holding one awesome good and every dummy one copy of the good (an EF+PO allocation), every
positive `α` makes `x` maximize `φ`, and the dual `p = 0`, `q_i = max_j α_i u′_ij` is optimal (its
value equals `φ(x)`), so every budget is `0`. The hypothesis `2 ≤ n` is added (as for
Lemma 15, on which the proof rests). -/
theorem lemma_16 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (hn : 2 ≤ n) :
    ∃ i, ¬ P.IsDummy i ∧ 0 < P.budget x α q i := by sorry

end CardinalMatching
