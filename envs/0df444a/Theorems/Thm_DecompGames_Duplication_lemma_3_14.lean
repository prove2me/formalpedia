-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_3_14
-- name    : DecompGames.Duplication.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:37.41741+00:00
-- url     : https://prove2.me/theorems/39a71b77-40a4-4fe2-92be-bdf8c6613d4b
-- title:
--   Lemma 3.14 (corrected: the extended co-measure copies γ) — extensions preserve γ-potential, nonstrategic, μ-normalized and (μ,γ)-harmonic games
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\pi=(\pi^j:S'^j\to S^j)_{j\in N}$ be a collapsing map, $\check g^j(s')=g^j(\pi(s'))$ the extended game and $\check\gamma^j(s')=\gamma^j(\pi(s'))$ the extended co-measure vector (the extending map $\check T$ applied to $\gamma$), and let $\check\mu$ be a strictly positive extension of $\mu$: $\sum_{b:\pi^j(b)=a}\check\mu^j(b)=\mu^j(a)$ for all $j$ and $a\in S^j$. Duplicating the strategy $s^i_1$ of player $i$ into $s^i_0,s^i_1$ (Definition 3.13) is the case $S'^i=S^i\cup\{s^i_0\}$, $\pi^i(s^i_0)=s^i_1$, all other $\pi$'s the identity. For every game $g$:
--
--   1. (i) if $g$ is $\gamma$-potential, then $\check g$ is $\check\gamma$-potential;
--   2. (ii) if $g$ is nonstrategic, then $\check g$ is nonstrategic;
--   3. (iii) if $g$ is $\mu$-normalized, then $\check g$ is $\check\mu$-normalized;
--   4. (iv) if $g$ is $(\mu,\gamma)$-harmonic, then $\check g$ is $(\check\mu,\check\gamma)$-harmonic.
--
--   Each class of the decomposition is mapped into the corresponding class of the extended game; with uniqueness of the decomposition this gives Theorem 3.15.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - generalization: a single duplication: Šⁱ = Sⁱ ∪ {s⁰ⁱ}, ǧ(s⁰ⁱ, s⁻ⁱ) = g(s¹ⁱ, s⁻ⁱ), μ̌ⁱ(s⁰ⁱ) + μ̌ⁱ(s¹ⁱ) = μⁱ(s¹ⁱ), μ̌ = μ elsewhere (Definition 3.13) → any family of collapsing maps πʲ : S'ʲ → Sʲ, with ǧʲ(s') = gʲ(π(s')) (extend π g) and μ' strictly positive with ∑_{b ∈ (πʲ)⁻¹(a)} μ'ʲ(b) = μʲ(a) (IsMeasureExtension); reason: Definition 3.13 is the case S'ⁱ = Sⁱ ∪ {s⁰ⁱ}, πⁱ(s⁰ⁱ) = s¹ⁱ, πⁱ = id on Sⁱ, πʲ = id for j ≠ i, where the fibre condition is exactly (i)–(ii) of the extension of μ; the Lean statement also covers several duplications at once
--   - encoding: μ̌ an extension of μ (a measure, strictly positive as every measure of Definition 2.2) → μ' with the hypothesis IsMeasureVec μ' (0 < μ' i b); reason: the classes of Definition 2.2 are defined for strictly positive measures
--   - correction: γ̌ an extension of γ: γ̌ⁱ(s⁻ⁱ) = γ⁻ⁱ(s⁻ⁱ) and, for j ≠ i, γ̌ʲ(s⁰ⁱ, s^{−(i,j)}) + γ̌ʲ(s¹ⁱ, s^{−(i,j)}) = γʲ(s¹ⁱ, s^{−(i,j)}) (Definition 3.13) → γ̌ = Ť(γ), γ̌ʲ(s') = γʲ(π(s')): γ̌ⁱ = γⁱ and γ̌ʲ(s⁰ⁱ, ·) = γ̌ʲ(s¹ⁱ, ·) = γʲ(s¹ⁱ, ·); reason: with the printed sum (i) is false: two players, Sʲ = {sʲ, tʲ}, μ ≡ 1, γ ≡ 1, g¹ = g² = Ψ with Ψ(s¹,s²) = Ψ(t¹,t²) = 1, Ψ(s¹,t²) = Ψ(t¹,s²) = −1 (γ-potential); duplicate s¹ with μ̌¹ = (½, ½, 1) and γ̌²(s¹₀,·) = γ̌²(s¹₁,·) = ½; a γ̌-potential Ψ̌ of ǧ would need Ψ̌(t¹,t²) − Ψ̌(t¹,s²) = 3 ≠ 2 = g²(t¹,t²) − g²(t¹,s²). The proof on p. 40 uses the copy, which also makes γ̌ unique ("the extension of γ"); γ⁻ⁱ in (i) is read as γⁱ
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 18, Lemma 3.14 and Definition 3.13; p. 40, proof of Lemma 3.14(iv)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Extension

namespace DecompGames.Duplication

open Finset

/-- Lemma 3.14, p. 18, for an extension along any collapsing map `π` (a single duplication is the
case of Definition 3.13), with the extended co-measure `γ̌ = Ť(γ)` (`γ̌ʲ(s') = γʲ(π(s'))`):
(i) `γ`-potential ⇒ `ǧ` is `γ̌`-potential; (ii) nonstrategic ⇒ `ǧ` nonstrategic;
(iii) `μ`-normalized ⇒ `ǧ` is `μ̌`-normalized; (iv) `(μ, γ)`-harmonic ⇒ `ǧ` is `(μ̌, γ̌)`-harmonic. -/
theorem lemma_3_14 {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Fintype (S' i)] [∀ i, DecidableEq (S' i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ)
    (π : ∀ i, S' i → S i) (μ' : ∀ i, S' i → ℝ) (hμ' : IsMeasureVec μ')
    (hext : IsMeasureExtension π μ μ') (g : Game ι S) :
    (IsPotential γ g → IsPotential (extend π γ) (extend π g)) ∧
    (IsNonstrategic g → IsNonstrategic (extend π g)) ∧
    (IsNormalized μ g → IsNormalized μ' (extend π g)) ∧
    (IsHarmonic μ γ g → IsHarmonic μ' (extend π γ) (extend π g)) := by sorry

end DecompGames.Duplication
