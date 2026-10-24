-- Prove2me | Theorems.Thm_DecompGames_Duplication_proposition_2_10
-- name    : DecompGames.Duplication.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:00.537413+00:00
-- url     : https://prove2.me/theorems/0bd5fc6d-353f-42c6-b304-99c409bf1448
-- title:
--   Proposition 2.10 — G = μ-NoG ⊕_{μ,γ} NSG
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\langle g_1,g_2\rangle_{\mu,\gamma}=\sum_{i}\mu^i(S^i)\langle\gamma^ig_1^i,\gamma^ig_2^i\rangle_0$ with $\langle h,f\rangle_0=\sum_s\mu(s)h(s)f(s)$ (2.13)–(2.15). The space of games is the direct orthogonal sum of the $\mu$-normalized and the nonstrategic games:
--   $$\mathcal G=\mu\text{-}\mathsf{NoG}\oplus_{\mu,\gamma}\mathsf{NSG}. \qquad (2.16)$$
--   That is, every game $g$ can be written in exactly one way as $g=a+b$ with $a$ $\mu$-normalized and $b$ nonstrategic, and $\langle a,b\rangle_{\mu,\gamma}=0$ for every $\mu$-normalized $a$ and every nonstrategic $b$.
--
--   This is the first decomposition of the paper; with uniform $\mu^i$ and $\gamma^i$ it is the normalized/nonstrategic split of Candogan et al. (2011).
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: G is the direct ⟨·,·⟩_{μ,γ}-orthogonal sum ⊕_{μ,γ} of the classes → every game has exactly one representation as a sum of members of the classes (∃!), and members of different classes are ⟨·,·⟩_{μ,γ}-orthogonal; reason: this is the meaning of a direct orthogonal sum of subspaces; each class is a linear subspace
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 10, Proposition 2.10, (2.16)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Proposition 2.10, p. 10, (2.16): `G = μ-NoG ⊕_{μ,γ} NSG`. Every game is uniquely the sum of a
`μ`-normalized and a nonstrategic game, and the two classes are `⟨·,·⟩_{μ,γ}`-orthogonal. -/
theorem proposition_2_10 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, ∃! ab : Game ι S × Game ι S,
      IsNormalized μ ab.1 ∧ IsNonstrategic ab.2 ∧ g = ab.1 + ab.2) ∧
    ∀ a b : Game ι S, IsNormalized μ a → IsNonstrategic b → ipGame μ γ a b = 0 := by sorry

end DecompGames.Duplication
