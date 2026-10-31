-- Prove2me | Theorems.Thm_CardinalMatching_lemma_21
-- name    : CardinalMatching.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:56.894992+00:00
-- url     : https://prove2.me/theorems/00796cd7-c600-48ee-9567-3ea2b57f0369
-- title:
--   Lemma 21: agents with the same $\theta$ functions have equal budgets (corrected: $I'$ with $k\ge n^4/\varepsilon$)
-- statement:
--   Let $i,i'$ be agents of $I'$ with $\theta_i=\theta_{i'}$, i.e. $\theta_i(t)=\theta_{i'}(t)$ for every budget $t\ge 0$, where $\theta_i(t)$ is the set of goods that can be positive in an optimal bundle of agent $i$ at budget $t$ (Definition 20). Then
--   $$
--   b_i=b_{i'} .
--   $$
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
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 21, p.12; Definition 20, p.11

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context
import Definitions.Def_CardinalMatching_ModParams_theta

namespace CardinalMatching

/-- **Lemma 21** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.12): "Let i, i′ be two agents with θi = θi′, then bi = bi′."

`θ_i = θ_i′` is equality of the functions `t ↦ θ_i(t)` on `t ≥ 0` (Definition 20, p.11, with the
prices `p` of Step 2). Running context of Step 2 (`IsStep2Context`). -/
theorem lemma_21 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (i i' : P.Agent)
    (hθ : ∀ t : ℝ, 0 ≤ t → P.theta p i t = P.theta p i' t) :
    P.budget x α q i = P.budget x α q i' := by sorry

end CardinalMatching
