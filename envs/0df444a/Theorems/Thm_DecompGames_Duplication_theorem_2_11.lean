-- Prove2me | Theorems.Thm_DecompGames_Duplication_theorem_2_11
-- name    : DecompGames.Duplication.theorem_2_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:29.034483+00:00
-- url     : https://prove2.me/theorems/d1b2075f-26d6-421c-bf69-9a0fec21fe5b
-- title:
--   Theorem 2.11 — G = (μ-NoG ∩ γ-PG) ⊕_{μ,γ} (μ-NoG ∩ (μ,γ)-HG) ⊕_{μ,γ} NSG
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\langle\cdot,\cdot\rangle_{\mu,\gamma}$ be the inner product (2.15). The space of games is the direct orthogonal sum of the $\mu$-normalized $\gamma$-potential, the $\mu$-normalized $(\mu,\gamma)$-harmonic and the nonstrategic games:
--   $$\mathcal G=(\mu\text{-}\mathsf{NoG}\cap\gamma\text{-}\mathsf{PG})\oplus_{\mu,\gamma}(\mu\text{-}\mathsf{NoG}\cap(\mu,\gamma)\text{-}\mathsf{HG})\oplus_{\mu,\gamma}\mathsf{NSG}. \qquad (2.17)$$
--   That is:
--
--   1. every game $g$ has exactly one $(\mu,\gamma)$-decomposition $g=g_{(\mu,\gamma)\text{-NS}}+g_{(\mu,\gamma)\text{-P}}+g_{(\mu,\gamma)\text{-H}}$ (2.18) with $g_{(\mu,\gamma)\text{-NS}}$ nonstrategic, $g_{(\mu,\gamma)\text{-P}}$ $\mu$-normalized and $\gamma$-potential, and $g_{(\mu,\gamma)\text{-H}}$ $\mu$-normalized and $(\mu,\gamma)$-harmonic;
--   2. the three classes are pairwise orthogonal for $\langle\cdot,\cdot\rangle_{\mu,\gamma}$.
--
--   With uniform $\mu^i$ and $\gamma^i$ this is the decomposition of Candogan, Menache, Ozdaglar and Parrilo (2011); the weights make it possible to state invariance of the decomposition under strategic transformations such as duplication (Theorem 3.15).
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: the components g_{(μ,γ)-NS}, g_{(μ,γ)-P}, g_{(μ,γ)-H} of the (μ,γ)-decomposition (2.18) → a triple (n, p, h) with IsDecomposition μ γ g n p h: n ∈ NSG, p ∈ μ-NoG ∩ γ-PG, h ∈ μ-NoG ∩ (μ,γ)-HG, g = n + p + h; reason: by Theorem 2.11 the triple is unique, so it is the decomposition; the order (NS, P, H) is that of (2.18)
--   - encoding: G is the direct ⟨·,·⟩_{μ,γ}-orthogonal sum ⊕_{μ,γ} of the classes → every game has exactly one representation as a sum of members of the classes (∃!), and members of different classes are ⟨·,·⟩_{μ,γ}-orthogonal; reason: this is the meaning of a direct orthogonal sum of subspaces; each class is a linear subspace
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 10, Theorem 2.11, (2.17)–(2.18)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Theorem 2.11, p. 10, (2.17):
`G = (μ-NoG ∩ γ-PG) ⊕_{μ,γ} (μ-NoG ∩ (μ, γ)-HG) ⊕_{μ,γ} NSG`. Every game has exactly one
`(μ, γ)`-decomposition `(g_NS, g_P, g_H)`, and the three classes are pairwise orthogonal for
`⟨·,·⟩_{μ,γ}`. -/
theorem theorem_2_11 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, ∃! t : Game ι S × Game ι S × Game ι S,
      IsDecomposition μ γ g t.1 t.2.1 t.2.2) ∧
    (∀ p h : Game ι S, IsNormalized μ p → IsPotential γ p →
      IsNormalized μ h → IsHarmonic μ γ h → ipGame μ γ p h = 0) ∧
    (∀ p n : Game ι S, IsNormalized μ p → IsPotential γ p →
      IsNonstrategic n → ipGame μ γ p n = 0) ∧
    (∀ h n : Game ι S, IsNormalized μ h → IsHarmonic μ γ h →
      IsNonstrategic n → ipGame μ γ h n = 0) := by sorry

end DecompGames.Duplication
