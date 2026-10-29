-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_A_2
-- name    : DecompGames.Duplication.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:00.815497+00:00
-- url     : https://prove2.me/theorems/9781aa4f-d54c-4867-a648-b79ffd17bf9e
-- title:
--   Lemma A.2 — NoG = Ker Λ, NSG = Im Λ; Π and Λ are ⟨·,·⟩_{μ,γ}-orthogonal projections of G
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\Lambda(g)=(\Lambda^1(g^1),\dots,\Lambda^n(g^n))$ and $\Pi(g)=(\Pi^1(g^1),\dots,\Pi^n(g^n))$ (A.5)–(A.6), with $\Lambda^i,\Pi^i$ as in (A.1), and let $\langle\cdot,\cdot\rangle_{\mu,\gamma}$ be the inner product (2.15). Then:
--
--   1. (a) The $\mu$-normalized games are exactly the games with $g^i\in\mathsf{NoG}^i$ for every $i$, and exactly the kernel of $\Lambda$; the nonstrategic games are exactly the games with $g^i\in\mathsf{NSG}^i$ for every $i$, and exactly the image of $\Lambda$:
--   $$\mu\text{-}\mathsf{NoG}=\{g:\forall i,\ g^i\in\mathsf{NoG}^i\}=\operatorname{Ker}\Lambda,\qquad \mathsf{NSG}=\{g:\forall i,\ g^i\in\mathsf{NSG}^i\}=\operatorname{Im}\Lambda.$$
--   2. (b) $\Pi$ and $\Lambda$ are orthogonal projections of $\mathcal G$ for $\langle\cdot,\cdot\rangle_{\mu,\gamma}$: they are linear and idempotent, and $\langle\Lambda(g_1),\Pi(g_2)\rangle_{\mu,\gamma}=0$ for all games $g_1,g_2$.
--
--   Part (b) is the orthogonality behind the direct sum $\mathcal G=\mu\text{-}\mathsf{NoG}\oplus_{\mu,\gamma}\mathsf{NSG}$ of Proposition 2.10.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: NSGⁱ: h(sⁱ, s⁻ⁱ) = ℓ(s⁻ⁱ) for some ℓ : S⁻ⁱ → ℝ (A.2) → h (Function.update s i a) = h s for all s, a (IsNSGi); reason: a function on S is of the form ℓ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: Π and Λ are orthogonal projections onto G for ⟨·,·⟩_{μ,γ} → Λ and Π are linear, idempotent, and ⟨Λ(g₁), Π(g₂)⟩_{μ,γ} = 0 for all g₁, g₂; reason: Π = Id − Λ, so Im Λ = Ker Π and Im Π = Ker Λ; an idempotent linear map is an orthogonal projection exactly when its image is orthogonal to its kernel
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 25, Lemma A.2, (A.7)–(A.8)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Lemma A.2, p. 25: (a) `NoG = {g : ∀ i, gⁱ ∈ NoGⁱ} = Ker Λ` (A.7) and
`NSG = {g : ∀ i, gⁱ ∈ NSGⁱ} = Im Λ` (A.8); (b) `Π` and `Λ` are orthogonal projections of `G` for
`⟨·,·⟩_{μ,γ}`. -/
theorem lemma_A_2 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, ((IsNormalized μ g ↔ ∀ i, IsNoGi μ i (g i)) ∧
        (IsNormalized μ g ↔ lamGame μ g = 0)) ∧
      ((IsNonstrategic g ↔ ∀ i, IsNSGi i (g i)) ∧
        (IsNonstrategic g ↔ g ∈ Set.range (lamGame μ)))) ∧
    ((IsLinearMap ℝ (lamGame μ) ∧ IsLinearMap ℝ (projGame μ)) ∧
      (lamGame μ ∘ lamGame μ = lamGame μ ∧ projGame μ ∘ projGame μ = projGame μ) ∧
      ∀ g₁ g₂ : Game ι S, ipGame μ γ (lamGame μ g₁) (projGame μ g₂) = 0) := by sorry

end DecompGames.Duplication
