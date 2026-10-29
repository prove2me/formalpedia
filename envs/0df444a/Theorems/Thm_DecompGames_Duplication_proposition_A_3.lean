-- Prove2me | Theorems.Thm_DecompGames_Duplication_proposition_A_3
-- name    : DecompGames.Duplication.proposition_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:00.917313+00:00
-- url     : https://prove2.me/theorems/3288b79d-25da-44a2-bb5d-f846738fa5a4
-- title:
--   Proposition A.3 — the adjoint of δⁱ is δⁱ*X(s) = −∑ₜ μ(t)Wⁱ(s,t)X(s,t) = −∑_{t:(s,t)∈Eⁱ} μⁱ(tⁱ)√μ⁻ⁱ(s⁻ⁱ) X(s,t)
-- statement:
--   Let $N$ be a finite set of players with finite strategy sets $S^i$, $S=\prod_iS^i$, and let $\mu^i$ be strictly positive measures on $S^i$ with product measure $\mu(s)=\prod_i\mu^i(s^i)$ and $\mu^{-i}(s^{-i})=\prod_{j\ne i}\mu^j(s^j)$. On $C_0=\{h:S\to\mathbb R\}$ take $\langle h,f\rangle_0=\sum_s\mu(s)h(s)f(s)$, and on the flows $C_1=\{X:S\times S\to\mathbb R,\ X(s,t)=-X(t,s)\}$ take $\langle X,Y\rangle_1=\tfrac12\sum_{s,t}\mu(s)\mu(t)X(s,t)Y(s,t)$. Let $E^i$ be the $i$-comparable pairs ($i$ is the only player with $s^i\ne t^i$), $W^i(s,t)=1/\sqrt{\mu^{-i}(s^{-i})}$ on $E^i$ and $0$ elsewhere, and $\delta^i(h)(s,t)=W^i(s,t)(h(t)-h(s))$.
--
--   Fix a player $i$ and let
--   $$\delta^{i*}X(s)=-\sum_{t\in S}\mu(t)\,W^i(s,t)\,X(s,t). \qquad (A.15)$$
--   Then $\delta^{i*}$ is the adjoint of $\delta^i$: for every flow $X\in C_1$, $\delta^{i*}X$ is the unique $f\in C_0$ with $\langle\delta^ih,X\rangle_1=\langle h,f\rangle_0$ for all $h\in C_0$ (A.14). Moreover, for every flow $X$ and every $s\in S$,
--   $$\delta^{i*}X(s)=-\sum_{t:\,(s,t)\in E^i}\mu^i(t^i)\sqrt{\mu^{-i}(s^{-i})}\,X(s,t). \qquad (A.16)$$
--
--   This is the explicit form of the adjoint gradient used to express harmonicity as $D(g)\in\operatorname{Ker}\delta^*$ (Proposition A.5).
--
--   Differences from the source:
--   - generalization: standing assumptions n ≥ 2 players and |Sⁱ| ≥ 2 strategies for every player (p. 7) → any finite type of players ι and any finite strategy sets S i, of any size; reason: the result holds without these assumptions (with an empty Sⁱ the space of profiles is empty and every game is 0); every instance of the source is an instance of the Lean statement
--   - encoding: μⁱ a strictly positive finite measure on Sⁱ → μ i : S i → ℝ, the point masses, with 0 < μ i a for all a (IsMeasureVec); reason: a measure on a finite set is determined by its point masses; μⁱ(Sⁱ) is mass μ i = ∑ₐ μ i a
--   - encoding: statements over s⁻ⁱ ∈ S⁻ⁱ and profiles (tⁱ, s⁻ⁱ) → statements over full profiles s : ∀ j, S j, with (tⁱ, s⁻ⁱ) written Function.update s i tⁱ; reason: the coordinate sⁱ of s is overwritten, so the quantifier ranges over the same subprofiles
--   - encoding: X ∈ C₁, the skew-symmetric functions on S × S (A.9) → X : S → S → ℝ with the hypothesis IsFlow X (X s t = −X t s); reason: same set of flows
--   - encoding: δⁱ* is the adjoint of δⁱ, the unique linear operator with ⟨δⁱh, X⟩₁ = ⟨h, δⁱ*X⟩₀ (A.14), and it satisfies (A.15) → deltaStar μ i is defined by (A.15), and for every flow X and every f : C₀, (∀ h, ⟨δⁱh, X⟩₁ = ⟨h, f⟩₀) ↔ f = deltaStar μ i X; reason: this says exactly that the adjoint, which is unique, is given by (A.15)
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 27, Proposition A.3, (A.14)–(A.16)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators

namespace DecompGames.Duplication

open Finset

open Classical in
/-- Proposition A.3, p. 27: the adjoint `δⁱ*` of `δⁱ` (for `⟨·,·⟩₁` on flows and `⟨·,·⟩₀` on `C₀`,
(A.14)) is given by (A.15), `δⁱ*X(s) = −∑_{t ∈ S} μ(t) Wⁱ(s, t) X(s, t)`, and (A.15) equals (A.16),
`−∑_{t : (s,t) ∈ Eⁱ} μⁱ(tⁱ) √(μ⁻ⁱ(s⁻ⁱ)) X(s, t)`. -/
theorem proposition_A_3 {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) :
    (∀ X : (∀ j, S j) → (∀ j, S j) → ℝ, IsFlow X →
      ∀ f : (∀ j, S j) → ℝ,
        (∀ h : (∀ j, S j) → ℝ, ip1 μ (delta μ i h) X = ip0 μ h f) ↔ f = deltaStar μ i X) ∧
    (∀ X : (∀ j, S j) → (∀ j, S j) → ℝ, IsFlow X → ∀ s : ∀ j, S j,
      deltaStar μ i X s =
        -∑ t ∈ univ.filter (fun t => IsComparable i s t),
          μ i (t i) * Real.sqrt (productMeasureExcept μ i s) * X s t) := by sorry

end DecompGames.Duplication
