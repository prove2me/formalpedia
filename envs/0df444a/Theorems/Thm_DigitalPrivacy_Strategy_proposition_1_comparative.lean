-- Prove2me | Theorems.Thm_DigitalPrivacy_Strategy_proposition_1_comparative
-- name    : DigitalPrivacy.Strategy.proposition_1_comparative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:39.019187+00:00
-- url     : https://prove2.me/theorems/f0adda3b-0b6c-4fdd-b5d3-a2230002f7da
-- title:
--   Proposition 1(a)–(b) with footnote 15, p. 10 — ā* and ξā* increase in C, and first increase then decrease in ξ
-- statement:
--   Let $0 \le \beta < 1$ and $0 \le \rho < 1$, and let $\bar a^*(\xi, C)$ be the equilibrium user activity of Proposition 1. Then:
--
--   1. **(a) Monotonicity in protection.** For every $\xi \in (0, 1]$, both $C \mapsto \bar a^*(\xi, C)$ and $C \mapsto \xi\bar a^*(\xi, C)$ are strictly increasing on $C > 0$.
--   2. **(b) Single peak in collection.** For every $C > 0$ there are thresholds $0 \le \underline\xi(C) \le \bar\xi(C) \le 1$ such that $\xi \mapsto \bar a^*(\xi, C)$ is strictly increasing on $[0, \underline\xi(C)]$ and strictly decreasing on $[\underline\xi(C), 1]$, and $\xi \mapsto \xi\bar a^*(\xi, C)$ is strictly increasing on $[0, \bar\xi(C)]$ and strictly decreasing on $[\bar\xi(C), 1]$.
--
--   This describes the trade-off a business faces: protection always raises activity and the data collected, while collecting more data raises activity only up to a point, and the total data collected only up to a later point.
--
--   **Formalization Note** Part (a) is stated for $\xi > 0$: at $\xi = 0$, $\bar a^*(0, C) = 1/(1-\beta)$ does not depend on $C$. Both parts are stated for $C > 0$, where the subgame equilibrium of Proposition 1 exists. The thresholds may equal $0$ or $1$ (the paper defines them as $\min\{1, \xi_1(C)\}$ and $\min\{1, \xi_2(C)\}$); "increases … and decreases otherwise" is read as strict monotonicity on the two closed pieces.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 10, Proposition 1 (a)–(b) and footnote 15; proof App. A.1, p. 28

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Strategy

/-- Proposition 1 (a)–(b) with footnote 15, p. 10: equilibrium activity `ā*(ξ, C)` and data
collected `ξ ā*(ξ, C)` (a) strictly increase in the protection level `C > 0` (for `ξ > 0`; at
`ξ = 0` activity does not depend on `C`), and (b) for each `C > 0` there are thresholds
`0 ≤ ξ₁ ≤ ξ₂ ≤ 1` such that `ā*(·, C)` strictly increases on `[0, ξ₁]` and strictly decreases on
`[ξ₁, 1]`, and `ξ ā*(ξ, C)` strictly increases on `[0, ξ₂]` and strictly decreases on `[ξ₂, 1]`. -/
theorem proposition_1_comparative (β ρ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) :
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 →
      StrictMonoOn (fun C => abar β ρ ξ C) (Set.Ioi 0) ∧
      StrictMonoOn (fun C => ξ * abar β ρ ξ C) (Set.Ioi 0)) ∧
    (∀ C : ℝ, 0 < C → ∃ ξ₁ ξ₂ : ℝ, 0 ≤ ξ₁ ∧ ξ₁ ≤ ξ₂ ∧ ξ₂ ≤ 1 ∧
      StrictMonoOn (fun ξ => abar β ρ ξ C) (Set.Icc 0 ξ₁) ∧
      StrictAntiOn (fun ξ => abar β ρ ξ C) (Set.Icc ξ₁ 1) ∧
      StrictMonoOn (fun ξ => ξ * abar β ρ ξ C) (Set.Icc 0 ξ₂) ∧
      StrictAntiOn (fun ξ => ξ * abar β ρ ξ C) (Set.Icc ξ₂ 1)) := by sorry

end DigitalPrivacy.Strategy
