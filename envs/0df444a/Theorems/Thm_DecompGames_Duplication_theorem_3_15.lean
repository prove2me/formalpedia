-- Prove2me | Theorems.Thm_DecompGames_Duplication_theorem_3_15
-- name    : DecompGames.Duplication.theorem_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:35.722664+00:00
-- url     : https://prove2.me/theorems/258bf274-5461-4b92-a2ee-44e273cf98b1
-- title:
--   Theorem 3.15 — duplicating a strategy commutes with the (μ,γ)-decomposition: the (μ̌,γ̌)-decomposition of ǧ is the extension of the (μ,γ)-decomposition of g
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\pi=(\pi^j:S'^j\to S^j)_{j\in N}$ be a collapsing map, $\check T$ the extending map $\check T(f)^j(s')=f^j(\pi(s'))$, $\check g=\check T(g)$, $\check\gamma=\check T(\gamma)$ the extended nonstrategic game of $\gamma$, and $\check\mu$ a strictly positive extension of $\mu$, $\sum_{b:\pi^j(b)=a}\check\mu^j(b)=\mu^j(a)$. Duplicating the strategy $s^i_1$ of player $i$ into $s^i_0,s^i_1$ (Definition 3.13) is the case $S'^i=S^i\cup\{s^i_0\}$, $\pi^i(s^i_0)=s^i_1$, all other $\pi$'s the identity.
--
--   Let $g$ be a game with $(\mu,\gamma)$-decomposition $(g_{(\mu,\gamma)\text{-NS}},g_{(\mu,\gamma)\text{-P}},g_{(\mu,\gamma)\text{-H}})$ (Theorem 2.11). Then the $(\check\mu,\check\gamma)$-decomposition of $\check g$ is the extension of that of $g$:
--   $$\check T\big(g_{(\mu,\gamma)\text{-NS}}\big)=(\check g)_{(\check\mu,\check\gamma)\text{-NS}},\qquad \check T\big(g_{(\mu,\gamma)\text{-P}}\big)=(\check g)_{(\check\mu,\check\gamma)\text{-P}},\qquad \check T\big(g_{(\mu,\gamma)\text{-H}}\big)=(\check g)_{(\check\mu,\check\gamma)\text{-H}}.$$
--   Equivalently: a triple $(n',p',h')$ of games on $S'$ is a $(\check\mu,\check\gamma)$-decomposition of $\check g$ if and only if $n'=\check T(g_{(\mu,\gamma)\text{-NS}})$, $p'=\check T(g_{(\mu,\gamma)\text{-P}})$ and $h'=\check T(g_{(\mu,\gamma)\text{-H}})$. Extensions and decompositions commute.
--
--   The decomposition is therefore insensitive to duplicated strategies, provided the measure is split among the copies and the co-measure is copied: strategically equivalent descriptions of a game have the same potential, harmonic and nonstrategic parts.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: the components g_{(μ,γ)-NS}, g_{(μ,γ)-P}, g_{(μ,γ)-H} of the (μ,γ)-decomposition (2.18) → a triple (n, p, h) with IsDecomposition μ γ g n p h: n ∈ NSG, p ∈ μ-NoG ∩ γ-PG, h ∈ μ-NoG ∩ (μ,γ)-HG, g = n + p + h; reason: by Theorem 2.11 the triple is unique, so it is the decomposition; the order (NS, P, H) is that of (2.18)
--   - generalization: a single duplication: Šⁱ = Sⁱ ∪ {s⁰ⁱ}, ǧ(s⁰ⁱ, s⁻ⁱ) = g(s¹ⁱ, s⁻ⁱ), μ̌ⁱ(s⁰ⁱ) + μ̌ⁱ(s¹ⁱ) = μⁱ(s¹ⁱ), μ̌ = μ elsewhere (Definition 3.13) → any family of collapsing maps πʲ : S'ʲ → Sʲ, with ǧʲ(s') = gʲ(π(s')) (extend π g) and μ' strictly positive with ∑_{b ∈ (πʲ)⁻¹(a)} μ'ʲ(b) = μʲ(a) (IsMeasureExtension); reason: Definition 3.13 is the case S'ⁱ = Sⁱ ∪ {s⁰ⁱ}, πⁱ(s⁰ⁱ) = s¹ⁱ, πⁱ = id on Sⁱ, πʲ = id for j ≠ i, where the fibre condition is exactly (i)–(ii) of the extension of μ; the Lean statement also covers several duplications at once
--   - encoding: μ̌ an extension of μ (a measure, strictly positive as every measure of Definition 2.2) → μ' with the hypothesis IsMeasureVec μ' (0 < μ' i b); reason: the classes of Definition 2.2 are defined for strictly positive measures
--   - reading: γ̌ the extended nonstrategic game of γ → γ̌ = Ť(γ) = extend π γ, γ̌ʲ(s') = γʲ(π(s')); reason: γ regarded as a nonstrategic game and extended by Ť, as on p. 19 ("the nonstrategic game γ is changed into γ̌ by also duplicating the strategy s¹ⁱ") and in the proof on p. 40; the sum-type extension of γ printed in Definition 3.13 makes the theorem false (counterexample in the Extension definition and in Lemma 3.14)
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 19, Theorem 3.15 (with Definition 3.13, p. 18; proof pp. 39–40)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Extension

namespace DecompGames.Duplication

open Finset

/-- Theorem 3.15, p. 19, for an extension along any collapsing map `π` (a single duplication is the
case of Definition 3.13): if `(n, p, h) = (g_{(μ,γ)-NS}, g_{(μ,γ)-P}, g_{(μ,γ)-H})` is the
`(μ, γ)`-decomposition of `g`, `μ̌` is an extension of `μ` and `γ̌ = Ť(γ)` is the extended
nonstrategic game of `γ`, then the `(μ̌, γ̌)`-decomposition of `ǧ = Ť(g)` is exactly
`(ň, p̌, ȟ)`: extensions and decompositions commute. -/
theorem theorem_3_15 {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Fintype (S' i)] [∀ i, DecidableEq (S' i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ)
    (π : ∀ i, S' i → S i) (μ' : ∀ i, S' i → ℝ) (hμ' : IsMeasureVec μ')
    (hext : IsMeasureExtension π μ μ')
    (g n p h : Game ι S) (hdec : IsDecomposition μ γ g n p h)
    (n' p' h' : Game ι S') :
    IsDecomposition μ' (extend π γ) (extend π g) n' p' h' ↔
      n' = extend π n ∧ p' = extend π p ∧ h' = extend π h := by sorry

end DecompGames.Duplication
