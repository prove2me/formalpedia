-- Prove2me | Theorems.Thm_DecompGames_Duplication_proposition_A_8
-- name    : DecompGames.Duplication.proposition_A_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:03.229207+00:00
-- url     : https://prove2.me/theorems/d5e9ea4c-2336-432b-93a3-9afc53e30d21
-- title:
--   Proposition A.8 — g ∈ μ-NoG ∩ (μ,γ)-HG iff ∑ᵢ μⁱ(Sⁱ)γⁱgⁱ = 0 and Π(g) = g
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\Pi(g)=(\Pi^1(g^1),\dots,\Pi^n(g^n))$ with $\Pi^i=\mathrm{Id}-\Lambda^i$ (A.1), (A.6). A game $g$ is a $\mu$-normalized $(\mu,\gamma)$-harmonic game if and only if
--   $$\sum_{i\in N}\mu^i(S^i)\,\gamma^i(s^{-i})\,g^i(s)=0\ \text{ for every } s\in S\qquad\text{and}\qquad\Pi(g)=g.$$
--
--   This characterization is what makes normalized potential and normalized harmonic games orthogonal (Proposition A.9).
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 31, Proposition A.8

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Proposition A.8, p. 31: `g` is a `μ`-normalized `(μ, γ)`-harmonic game iff
`∑_{i ∈ N} μⁱ(Sⁱ) γⁱ gⁱ = 0` and `Π(g) = g`. -/
theorem proposition_A_8 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    ∀ g : Game ι S, (IsNormalized μ g ∧ IsHarmonic μ γ g) ↔
      ((∀ s : ∀ j, S j, ∑ i, mass μ i * γ i s * g i s = 0) ∧ projGame μ g = g) := by sorry

end DecompGames.Duplication
