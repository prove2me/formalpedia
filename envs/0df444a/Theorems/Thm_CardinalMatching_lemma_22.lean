-- Prove2me | Theorems.Thm_CardinalMatching_lemma_22
-- name    : CardinalMatching.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:19.291438+00:00
-- url     : https://prove2.me/theorems/d571f7a6-bb82-466a-8540-37ce392dc48f
-- title:
--   Lemma 22: agents agreeing outside one type have at most $2n+1$ distinct $\theta$ functions (corrected: $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   Let $i_1,\dots,i_m$ be agents of $I'$ such that all of them agree on all utilities except possibly on the goods of one type (Definition 11). Then the functions $\theta_{i_1},\dots,\theta_{i_m}$ (on budgets $t\ge 0$, Definition 20) take at most $2n+1$ distinct values:
--   $$
--   \big|\{\theta_{i_1},\dots,\theta_{i_m}\}\big|\le 2n+1 ,
--   $$
--   where $n$ is the original number of agents. Along an interpolating chain, the optimal-bundle structure can therefore change only a bounded number of times.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$.
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
--   - reading: θ_i(t) is a set of goods "j ∈ G" (Definition 20) → θ_i(t) ⊆ G′; reason: LP (1) defining θ ranges over G′ (its constraint sums over j ∈ G′)
--   - generalization: the data rescaled to maximal non-dummy budget 1, assumed from Lemma 16 on (p.10) → the rescaling is not assumed; reason: the statement holds for every scale; it specializes to the rescaled data
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 22, p.12

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context
import Definitions.Def_CardinalMatching_ModParams_theta

namespace CardinalMatching

/-- **Lemma 22** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.12): "Let i1, . . . , im be a set of agents such that all agents agree
on all utilities except for possibly one type of good. Then |{θi1, . . . , θim}| ≤ 2n + 1."

The agents form a finite set `S` of agents of `I′`; they agree on every good not of the type of
some good `g₀` (Definition 11, p.7). The functions `θ_i` (Definition 20, p.11) are compared on
`t ≥ 0`; `n` is the original number of agents. Running context of Step 2 (`IsStep2Context`). -/
theorem lemma_22 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (S : Finset P.Agent)
    (g₀ : P.Good)
    (hagree : ∀ a ∈ S, ∀ a' ∈ S, ∀ g, ¬ P.SameGoodType g g₀ → P.util a g = P.util a' g) :
    ((fun a => fun t : Set.Ici (0 : ℝ) => P.theta p a t) '' (S : Set P.Agent)).ncard ≤
      2 * n + 1 := by sorry

end CardinalMatching
