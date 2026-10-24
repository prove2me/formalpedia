-- Prove2me | Theorems.Thm_DecompGames_Duplication_proposition_A_9
-- name    : DecompGames.Duplication.proposition_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:14.083983+00:00
-- url     : https://prove2.me/theorems/e3bbc84e-d0ca-49c5-8433-9a68c3ab1b7a
-- title:
--   Proposition A.9 — NoG ∩ (μ,γ)-HG, NoG ∩ γ-PG and NSG are pairwise ⟨·,·⟩_{μ,γ}-orthogonal
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\langle\cdot,\cdot\rangle_{\mu,\gamma}$ be the inner product (2.15). The three classes $\mu\text{-}\mathsf{NoG}\cap(\mu,\gamma)\text{-}\mathsf{HG}$, $\mu\text{-}\mathsf{NoG}\cap\gamma\text{-}\mathsf{PG}$ and $\mathsf{NSG}$ are pairwise orthogonal:
--
--   1. $\langle g_P,g_H\rangle_{\mu,\gamma}=0$ whenever $g_P$ is $\mu$-normalized and $\gamma$-potential and $g_H$ is $\mu$-normalized and $(\mu,\gamma)$-harmonic;
--   2. $\langle g_P,g_N\rangle_{\mu,\gamma}=0$ whenever $g_P$ is $\mu$-normalized and $\gamma$-potential and $g_N$ is nonstrategic;
--   3. $\langle g_H,g_N\rangle_{\mu,\gamma}=0$ whenever $g_H$ is $\mu$-normalized and $(\mu,\gamma)$-harmonic and $g_N$ is nonstrategic.
--
--   Together with Lemma A.11 this yields Theorem 2.11.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 31, Proposition A.9

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Proposition A.9, p. 31: `NoG ∩ (μ, γ)-HG`, `NoG ∩ γ-PG` and `NSG` are pairwise orthogonal for
`⟨·,·⟩_{μ,γ}` (2.15). -/
theorem proposition_A_9 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ p h : Game ι S, IsNormalized μ p → IsPotential γ p →
      IsNormalized μ h → IsHarmonic μ γ h → ipGame μ γ p h = 0) ∧
    (∀ p n : Game ι S, IsNormalized μ p → IsPotential γ p →
      IsNonstrategic n → ipGame μ γ p n = 0) ∧
    (∀ h n : Game ι S, IsNormalized μ h → IsHarmonic μ γ h →
      IsNonstrategic n → ipGame μ γ h n = 0) := by sorry

end DecompGames.Duplication
