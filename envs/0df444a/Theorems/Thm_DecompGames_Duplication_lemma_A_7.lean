-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_A_7
-- name    : DecompGames.Duplication.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:05.247304+00:00
-- url     : https://prove2.me/theorems/76f3d07d-d334-4a20-b790-90a7ec552a8e
-- title:
--   Lemma A.7 — δⁱ* ∘ δⁱ = μⁱ(Sⁱ) Πⁱ
-- statement:
--   Let $N$ be a finite set of players with finite strategy sets $S^i$, $S=\prod_iS^i$, and let $\mu^i$ be strictly positive measures on $S^i$, with total masses $\mu^i(S^i)$ and product measure $\mu(s)$. Let $\delta^i(h)(s,t)=W^i(s,t)(h(t)-h(s))$ (A.13) with the weights $W^i$ of (A.11), $\delta^{i*}X(s)=-\sum_t\mu(t)W^i(s,t)X(s,t)$ (A.15), and $\Pi^i=\mathrm{Id}-\Lambda^i$ with $\Lambda^i(h)(s)=\sum_{t^i}\bar\mu^i(t^i)h(t^i,s^{-i})$ (A.1). Then for every player $i$,
--   $$\delta^{i*}\circ\delta^i=\mu^i(S^i)\,\Pi^i. \qquad (A.24)$$
--
--   The one-player Laplacian is thus a multiple of the projection onto $\mathsf{NoG}^i$, which links normalization and harmonicity in Proposition A.8.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: δⁱ* the adjoint of δⁱ, characterized by (A.14); δ* = ∑ᵢ δⁱ* → deltaStar μ i, defined by the explicit formula (A.15); deltaStarAll = ∑ᵢ deltaStar μ i; reason: Proposition A.3 (a milestone of this mission) states that the formula is the adjoint on flows, and every flow appearing here (δⁱh, D(g)) is skew-symmetric
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 30, Lemma A.7, (A.24)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Lemma A.7, p. 30, (A.24): `δⁱ* ∘ δⁱ = μⁱ(Sⁱ) Πⁱ`. -/
theorem lemma_A_7 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) :
    ∀ h : (∀ j, S j) → ℝ, deltaStar μ i (delta μ i h) = fun s => mass μ i * proj μ i h s := by sorry

end DecompGames.Duplication
