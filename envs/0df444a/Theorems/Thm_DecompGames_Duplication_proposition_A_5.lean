-- Prove2me | Theorems.Thm_DecompGames_Duplication_proposition_A_5
-- name    : DecompGames.Duplication.proposition_A_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:02.315291+00:00
-- url     : https://prove2.me/theorems/daa48fd5-6102-4671-841e-9f25a00ba68b
-- title:
--   Proposition A.5 — NSG = {D(g) = 0}, γ-PG = D⁻¹(Im δ), (μ,γ)-HG = {D(g) ∈ Ker δ*}
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   With $\delta=\sum_i\delta^i$, $\delta^*=\sum_i\delta^{i*}$ (A.13), (A.15) and $D(g)=\sum_i\delta^i(\gamma^ig^i)$ (A.18):
--
--   1. (a) $g$ is nonstrategic if and only if $D(g)=0$.
--   2. (b) $g$ is $\gamma$-potential if and only if $D(g)\in\operatorname{Im}\delta$, i.e. $D(g)=\delta\varphi$ for some $\varphi:S\to\mathbb R$.
--   3. (c) $g$ is $(\mu,\gamma)$-harmonic if and only if $D(g)\in\operatorname{Ker}\delta^*$, i.e. $\delta^*(D(g))(s)=0$ for every $s\in S$.
--
--   These characterizations translate the three classes of Definition 2.2 into the language of flows on the game graph.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: δⁱ* the adjoint of δⁱ, characterized by (A.14); δ* = ∑ᵢ δⁱ* → deltaStar μ i, defined by the explicit formula (A.15); deltaStarAll = ∑ᵢ deltaStar μ i; reason: Proposition A.3 (a milestone of this mission) states that the formula is the adjoint on flows, and every flow appearing here (δⁱh, D(g)) is skew-symmetric
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 29, Proposition A.5

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Proposition A.5, p. 29: (a) `NSG = {g : D(g) = 0}`; (b) `γ-PG = D⁻¹(Im δ)`;
(c) `(μ, γ)-HG = {g : D(g) ∈ Ker δ*}`. -/
theorem proposition_A_5 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, IsNonstrategic g ↔ embed μ γ g = 0) ∧
    (∀ g : Game ι S, IsPotential γ g ↔ ∃ φ : (∀ j, S j) → ℝ, embed μ γ g = deltaAll μ φ) ∧
    (∀ g : Game ι S, IsHarmonic μ γ g ↔ deltaStarAll μ (embed μ γ g) = 0) := by sorry

end DecompGames.Duplication
