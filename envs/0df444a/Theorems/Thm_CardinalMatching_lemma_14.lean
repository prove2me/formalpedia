-- Prove2me | Theorems.Thm_CardinalMatching_lemma_14
-- name    : CardinalMatching.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:55.852986+00:00
-- url     : https://prove2.me/theorems/2c044d80-ebcc-42cd-9b76-e80aef7b695c
-- title:
--   Lemma 14: goods of the same type have equal prices (corrected: $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   If $j$ and $j'$ are goods of $I'$ of the same type (every agent of $I'$ values them equally, Definition 11), then
--   $$
--   p_j = p_{j'} .
--   $$
--   In particular all copies of an original good share one price, which defines the contracted prices $\hat p$.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$.
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 14, p.9; Definition 11, p.7

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

/-- **Lemma 14** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.9): "If j and j′ are goods of the same type, then pj = pj′."

"Same type" is Definition 11 (p.7) in `I′`: all agents of `I′` have identical utilities for
`j` and `j′`. Running context of Step 2 (`IsStep2Context`). -/
theorem lemma_14 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (j j' : P.Good)
    (h : P.SameGoodType j j') : p j = p j' := by sorry

end CardinalMatching
