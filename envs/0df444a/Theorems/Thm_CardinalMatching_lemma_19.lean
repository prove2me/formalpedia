-- Prove2me | Theorems.Thm_CardinalMatching_lemma_19
-- name    : CardinalMatching.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:10.1192+00:00
-- url     : https://prove2.me/theorems/c07efa5f-5f20-47c5-9d65-b9661991499c
-- title:
--   Lemma 19: agents differing by at most $\varepsilon$ on one type have budgets within $5n^2\varepsilon$ (corrected: $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   Let $i,i'$ be non-dummy agents of $I'$ whose utilities are identical except on the goods of one type (Definition 11), where they differ by at most $\varepsilon$. Then
--   $$
--   |b_i-b_{i'}|\le 5n^2\varepsilon ,
--   $$
--   where $n$ is the original number of agents and $\varepsilon$ is the construction's step.
--
--   The statement is made in the running context of Step 2 (`IsStep2Context`): admissible parameters of $I'$ (with correction C1), an EF+PO allocation $x$ of $I'$, positive weights $\alpha$ for which $x$ maximizes $\varphi$, and an optimal dual $(p,q)\ge 0$, with budgets $b_i=\alpha_i u'_i\cdot x_i-q_i$. After Lemma 16 the data are rescaled so that the largest budget of a non-dummy agent is $1$ (`IsRescaled`).
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: a rational EF+PO allocation x on I′ (p.8) built from rational utilities → any real EF+PO allocation x of I′, real utilities in [0,1]; reason: the statement does not use rationality; it specializes to the rational case
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 19, p.10

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

/-- **Lemma 19** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.10): "Let i, i′ be two non-dummy agents whose utilities are identical
except for the goods of one type where they differ by at most ǫ. Then |bi − bi′| ≤ 5n²ǫ."

The type is a class of Definition 11 (p.7) in `I′` (the goods of the same type as some good
`g₀`). After the rescaling of p.10 (`IsRescaled`); `n` is the original number of agents and `ε`
the construction's step. -/
theorem lemma_19 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q)
    (hR : P.IsRescaled x α q) (i i' : P.Agent) (hi : ¬ P.IsDummy i) (hi' : ¬ P.IsDummy i')
    (g₀ : P.Good) (hsame : ∀ g, ¬ P.SameGoodType g g₀ → P.util i g = P.util i' g)
    (hclose : ∀ g, P.SameGoodType g g₀ → |P.util i g - P.util i' g| ≤ P.ε) :
    |P.budget x α q i - P.budget x α q i'| ≤ 5 * (n : ℝ) ^ 2 * P.ε := by sorry

end CardinalMatching
