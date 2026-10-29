-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_A_1
-- name    : DecompGames.Duplication.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:00.103239+00:00
-- url     : https://prove2.me/theorems/c6adf040-9ef8-4f1d-850a-99c35ed3868c
-- title:
--   Lemma A.1 — Λⁱ, Πⁱ are projections of C₀; γⁱ Ker Λⁱ ⊥₀ γⁱ Im Λⁱ; NoGⁱ = Ker Λⁱ, NSGⁱ = Im Λⁱ
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\Lambda^i(h)(s^i,s^{-i})=\sum_{t^i}\bar\mu^i(t^i)h(t^i,s^{-i})$ with $\bar\mu^i=\mu^i/\mu^i(S^i)$, and $\Pi^i=\mathrm{Id}_{C_0}-\Lambda^i$ (A.1), operators on $C_0=\{h:S\to\mathbb R\}$. Let $\mathsf{NSG}^i$ be the functions not depending on $s^i$ (A.2) and $\mathsf{NoG}^i$ the functions with $\sum_{s^i}\mu^i(s^i)h(s^i,s^{-i})=0$ for every $s^{-i}$ (A.3). Fix a player $i$. Then:
--
--   1. $\Lambda^i$ and $\Pi^i$ are projections of $C_0$: linear and idempotent, $\Lambda^i\circ\Lambda^i=\Lambda^i$, $\Pi^i\circ\Pi^i=\Pi^i$.
--   2. For every $h_{\mathrm{Ker}}\in\operatorname{Ker}\Lambda^i$ and every $h_{\mathrm{Im}}\in\operatorname{Im}\Lambda^i$,
--   $$\big\langle\gamma^ih_{\mathrm{Ker}},\gamma^ih_{\mathrm{Im}}\big\rangle_0=\sum_{s\in S}\mu(s)\,\gamma^i(s^{-i})^2\,h_{\mathrm{Ker}}(s)\,h_{\mathrm{Im}}(s)=0.$$
--   3. $\mathsf{NoG}^i=\operatorname{Ker}\Lambda^i$ and $\mathsf{NSG}^i=\operatorname{Im}\Lambda^i$.
--
--   This identifies the normalized and nonstrategic parts of one payoff function with the kernel and image of a single orthogonal projection, the first step towards Proposition 2.10.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: NSGⁱ: h(sⁱ, s⁻ⁱ) = ℓ(s⁻ⁱ) for some ℓ : S⁻ⁱ → ℝ (A.2) → h (Function.update s i a) = h s for all s, a (IsNSGi); reason: a function on S is of the form ℓ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: Λⁱ and Πⁱ are projections onto C₀ → Λⁱ and Πⁱ are ℝ-linear (IsLinearMap) and idempotent (Λⁱ ∘ Λⁱ = Λⁱ, Πⁱ ∘ Πⁱ = Πⁱ); reason: a projection of a vector space is an idempotent linear map
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 24, Lemma A.1 (with (A.1)–(A.3))

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Lemma A.1, p. 24: `Λⁱ` and `Πⁱ` are (linear, idempotent) projections of `C₀`; `γⁱ`-scaled
kernel and image of `Λⁱ` are `⟨·,·⟩₀`-orthogonal; `NoGⁱ = Ker Λⁱ` and `NSGⁱ = Im Λⁱ`. -/
theorem lemma_A_1 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) (i : ι) :
    ((IsLinearMap ℝ (lam μ i) ∧ IsLinearMap ℝ (proj μ i)) ∧
      (lam μ i ∘ lam μ i = lam μ i ∧ proj μ i ∘ proj μ i = proj μ i)) ∧
    (∀ hKer hIm : (∀ j, S j) → ℝ, lam μ i hKer = 0 → hIm ∈ Set.range (lam μ i) →
      ip0 μ (coScale γ i hKer) (coScale γ i hIm) = 0) ∧
    ((∀ h : (∀ j, S j) → ℝ, IsNoGi μ i h ↔ lam μ i h = 0) ∧
      (∀ h : (∀ j, S j) → ℝ, IsNSGi i h ↔ h ∈ Set.range (lam μ i))) := by sorry

end DecompGames.Duplication
