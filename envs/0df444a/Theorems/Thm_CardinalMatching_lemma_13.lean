-- Prove2me | Theorems.Thm_CardinalMatching_lemma_13
-- name    : CardinalMatching.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:55.663727+00:00
-- url     : https://prove2.me/theorems/031538a1-6384-4bfd-a784-d98e2a2758f3
-- title:
--   Lemma 13: budgets are non-negative and every bundle is optimal at its budget (corrected: $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   For every agent $i$ of $I'$, $b_i\ge 0$, and $x_i$ is an optimum solution of
--   $$
--   \max\ u'_i\cdot y\quad\text{s.t.}\quad \sum_{j\in G'}y_j\le 1,\quad p\cdot y\le b_i,\quad y\ge 0 .
--   $$
--   So $x$ together with the prices $p$ and budgets $b$ is a competitive equilibrium of $I'$, a version of the second welfare theorem.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$.
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 13, p.9

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context
import Definitions.Def_CardinalMatching_ModParams_theta

namespace CardinalMatching

/-- **Lemma 13** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.9): "For every agent i, we have that bi ≥ 0 and xi is an optimum
solution to max ui · xi s.t. ∑_{j∈G′} xij ≤ 1, p · xi ≤ bi, xi ≥ 0."

Here `b_i = α_i u_i · x_i − q_i` and `(p, q)` is an optimal dual solution with `p, q ≥ 0`, in the
running context of Step 2 (`IsStep2Context`, including correction C1 for `I′`). -/
theorem lemma_13 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (i : P.Agent) :
    0 ≤ P.budget x α q i ∧ P.IsOptBundle p i (P.budget x α q i) (x i) := by sorry

end CardinalMatching
