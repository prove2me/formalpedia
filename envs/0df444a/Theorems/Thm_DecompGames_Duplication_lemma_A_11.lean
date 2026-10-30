-- Prove2me | Theorems.Thm_DecompGames_Duplication_lemma_A_11
-- name    : DecompGames.Duplication.lemma_A_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:23.727248+00:00
-- url     : https://prove2.me/theorems/fa394724-22b2-4c55-a4f8-45ac9a682149
-- title:
--   Lemma A.11 — g = Π(h) + Π(g − h) + Λ(g) is the (μ,γ)-decomposition, hⁱ = φ/γⁱ, φ any solution of δ*δφ = δ*D(g) (e.g. δ†D(g))
-- statement:
--   Let $N$ be a finite set of players; player $i$ has a finite strategy set $S^i$, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$; $\mathcal G$ is the space of games. For $i\in N$ let $\mu^i$ be a strictly positive measure on $S^i$, $\mu(s)=\prod_i\mu^i(s^i)$ the product measure, $\mu^i(S^i)=\sum_{t^i}\mu^i(t^i)$, and let $\gamma=(\gamma^i)_{i\in N}$ be a co-measure vector, $\gamma^i$ a strictly positive function of $s^{-i}$.
--
--   Let $\Lambda,\Pi$ be as in (A.5)–(A.6), $\delta=\sum_i\delta^i$, $\delta^*=\sum_i\delta^{i*}$ and $D(g)=\sum_i\delta^i(\gamma^ig^i)$ (A.18). Fix a game $g$.
--
--   1. The normal equation $\delta^*\delta\varphi=\delta^*D(g)$ has a solution $\varphi:S\to\mathbb R$ (for instance $\varphi=\delta^\dagger D(g)$, with $\delta^\dagger$ the Moore–Penrose pseudo-inverse of $\delta$).
--   2. For every solution $\varphi$, let $h=\big(\tfrac1{\gamma^1}\varphi,\dots,\tfrac1{\gamma^n}\varphi\big)$ (A.26) and
--   $$g_P=\Pi(h),\qquad g_H=\Pi(g-h),\qquad g_{NSG}=\Lambda(g). \qquad (A.25)$$
--   Then $g=g_P+g_H+g_{NSG}$ (A.27), $g_P$ is $\gamma$-potential and $\mu$-normalized, $g_H$ is $(\mu,\gamma)$-harmonic and $\mu$-normalized, and $g_{NSG}$ is nonstrategic; so $(g_{NSG},g_P,g_H)$ is the $(\mu,\gamma)$-decomposition of $g$.
--
--   This is the existence half of Theorem 2.11, with an explicit formula for the components.
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: γⁱ a co-measure, a strictly positive measure on S⁻ⁱ (Definition 2.1) → γ i : (∀ j, S j) → ℝ positive with γ i (Function.update s i a) = γ i s (IsCoMeasureVec); reason: functions on S⁻ⁱ are exactly the functions on S that do not depend on the coordinate sⁱ
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: g nonstrategic: for each i there is ℓⁱ : S⁻ⁱ → ℝ with gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ) (2.4) → gⁱ(Function.update s i a) = gⁱ(s) for all i, s, a (IsNonstrategic); reason: a function on S is of the form ℓⁱ(s⁻ⁱ) exactly when it does not depend on sⁱ
--   - encoding: δⁱ* the adjoint of δⁱ, characterized by (A.14); δ* = ∑ᵢ δⁱ* → deltaStar μ i, defined by the explicit formula (A.15); deltaStarAll = ∑ᵢ deltaStar μ i; reason: Proposition A.3 (a milestone of this mission) states that the formula is the adjoint on flows, and every flow appearing here (δⁱh, D(g)) is skew-symmetric
--   - encoding: the components g_{(μ,γ)-NS}, g_{(μ,γ)-P}, g_{(μ,γ)-H} of the (μ,γ)-decomposition (2.18) → a triple (n, p, h) with IsDecomposition μ γ g n p h: n ∈ NSG, p ∈ μ-NoG ∩ γ-PG, h ∈ μ-NoG ∩ (μ,γ)-HG, g = n + p + h; reason: by Theorem 2.11 the triple is unique, so it is the decomposition; the order (NS, P, H) is that of (2.18)
--   - generalization: φ = δ†D(g), with δ† the Moore–Penrose pseudo-inverse of δ for ⟨·,·⟩₀ and ⟨·,·⟩₁ (A.26) → existence of a solution φ of δ*δφ = δ*D(g), and the conclusion for every such φ; reason: δδ† is the orthogonal projection onto Im δ, so (Id − δδ†)D(g) ∈ Ker δ* and φ = δ†D(g) solves the normal equation; the Lean statement specializes to the paper's φ
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 32, Lemma A.11, (A.25)–(A.27); p. 30 (δ†); p. 33 (the property of δ† used)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

/-- Lemma A.11, p. 32, with `δ†D(g)` replaced by any solution `φ` of the normal equation
`δ*δφ = δ*D(g)` (which `φ = δ†D(g)` solves): with `h = ((1/γ¹)φ, …, (1/γⁿ)φ)` (A.26), the games
`g_NSG = Λ(g)`, `g_P = Π(h)`, `g_H = Π(g − h)` (A.25) form the `(μ, γ)`-decomposition of `g` (A.27). -/
theorem lemma_A_11 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    ∀ g : Game ι S,
      (∃ φ : (∀ j, S j) → ℝ, deltaStarAll μ (deltaAll μ φ) = deltaStarAll μ (embed μ γ g)) ∧
      ∀ φ : (∀ j, S j) → ℝ, deltaStarAll μ (deltaAll μ φ) = deltaStarAll μ (embed μ γ g) →
        IsDecomposition μ γ g (lamGame μ g) (projGame μ (fun i s => φ s / γ i s))
          (projGame μ (g - fun i s => φ s / γ i s)) := by sorry

end DecompGames.Duplication
