-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_A_4
-- name    : DecompGames.Duplication.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:16.215966+00:00
-- url     : https://prove2.me/theorems/2a03a66d-5515-4af4-9fd9-29de85fb875b
-- title:
--   Lemma A.4 — δⁱ*δʲ = 0 (i ≠ j); δ*D(g) = ∑ᵢ δⁱ*δⁱ(γⁱgⁱ); δⁱ*δⁱ(γⁱh) = γⁱ δⁱ*δⁱ(h)
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   With the gradients $\delta^i(h)(s,t)=W^i(s,t)(h(t)-h(s))$ (A.13), their adjoints $\delta^{i*}X(s)=-\sum_t\mu(t)W^i(s,t)X(s,t)$ (A.15), $\delta^*=\sum_i\delta^{i*}$ and $D(g)=\sum_i\delta^i(\gamma^ig^i)$ (A.18):
--
--   1. (a) For all players $i\ne j$ and all $h\in C_0$, $\delta^{i*}\delta^jh=0$ (A.19).
--   2. (b) For every game $g$, $\delta^*D(g)=\sum_{i\in N}\delta^{i*}\delta^i(\gamma^ig^i)$ (A.20).
--   3. (c) For every player $i$ and every $h\in C_0$, $\delta^{i*}\delta^i(\gamma^ih)=\gamma^i\,\delta^{i*}\delta^i(h)$ (A.21).
--
--   These identities reduce $\delta^*D$ to a sum of one-player Laplacians, which Proposition A.8 needs.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: δⁱ* the adjoint of δⁱ, characterized by (A.14); δ* = ∑ᵢ δⁱ* → deltaStar μ i, defined by the explicit formula (A.15); deltaStarAll = ∑ᵢ deltaStar μ i; reason: Proposition A.3 (a milestone of this mission) states that the formula is the adjoint on flows, and every flow appearing here (δⁱh, D(g)) is skew-symmetric
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 28, Lemma A.4, (A.19)–(A.21)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Lemma A.4, p. 28: (a) `δⁱ*δʲ = 0` for `i ≠ j` (A.19); (b) `δ*D(g) = ∑_{i ∈ N} δⁱ*δⁱ(γⁱgⁱ)`
(A.20); (c) `δⁱ*δⁱ(γⁱh) = γⁱ δⁱ*δⁱ(h)` (A.21). -/
theorem lemma_A_4 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ i j : ι, i ≠ j → ∀ h : (∀ k, S k) → ℝ, deltaStar μ i (delta μ j h) = 0) ∧
    (∀ g : Game ι S, deltaStarAll μ (embed μ γ g) =
      fun s => ∑ i, deltaStar μ i (delta μ i (coScale γ i (g i))) s) ∧
    (∀ (i : ι) (h : (∀ k, S k) → ℝ),
      deltaStar μ i (delta μ i (coScale γ i h)) = coScale γ i (deltaStar μ i (delta μ i h))) := by sorry

end DecompGames.Duplication
