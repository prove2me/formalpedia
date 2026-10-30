-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_A_6
-- name    : DecompGames.Duplication.lemma_A_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:10.182342+00:00
-- url     : https://prove2.me/theorems/470458a3-171e-496a-b92c-c9d2a8176e21
-- title:
--   Lemma A.6 — φ ∈ NoGⁱ, δⁱφ = δⁱφ̃ ⇒ ⟨φ,ψ⟩₀ = ⟨φ̃,ψ⟩₀ for all ψ ∈ NoGⁱ
-- statement:
--   Let $N$ be a finite set of players with finite strategy sets $S^i$, $S=\prod_iS^i$, and let $\mu^i$ be strictly positive measures on $S^i$ with product measure $\mu(s)$; $\langle h,f\rangle_0=\sum_s\mu(s)h(s)f(s)$ (2.13). Let $\mathsf{NoG}^i$ be the functions $h:S\to\mathbb R$ with $\sum_{s^i}\mu^i(s^i)h(s^i,s^{-i})=0$ for every $s^{-i}$ (A.3), and $\delta^i(h)(s,t)=W^i(s,t)(h(t)-h(s))$ (A.13).
--
--   Fix a player $i$, let $\varphi\in\mathsf{NoG}^i$ and $\tilde\varphi:S\to\mathbb R$, and assume $\delta^i\varphi=\delta^i\tilde\varphi$. Then for every $\psi\in\mathsf{NoG}^i$,
--   $$\langle\varphi,\psi\rangle_0=\langle\tilde\varphi,\psi\rangle_0.$$
--
--   It is used in the orthogonality of normalized potential and normalized harmonic games (Proposition A.9).
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 30, Lemma A.6

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Lemma A.6, p. 30: if `φ ∈ NoGⁱ`, `φ̃ ∈ C₀` and `δⁱφ = δⁱφ̃`, then `⟨φ, ψ⟩₀ = ⟨φ̃, ψ⟩₀`
for every `ψ ∈ NoGⁱ`. -/
theorem lemma_A_6 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (φ φt : (∀ j, S j) → ℝ) (hφ : IsNoGi μ i φ) (hδ : delta μ i φ = delta μ i φt) :
    ∀ ψ : (∀ j, S j) → ℝ, IsNoGi μ i ψ → ip0 μ φ ψ = ip0 μ φt ψ := by sorry

end DecompGames.Duplication
