-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_budget_exhausted
-- name    : ArrowDebreu.ThmI.budget_exhausted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:38:51.874741+00:00
-- url     : https://prove2.me/theorems/b83dc806-1230-4f95-87bb-d881ed9cbabe
-- title:
--   Non-satiation exhausts the budget (§1.4.2 (1))
-- statement:
--   Let an economy satisfy Assumption II (each $X_i$ closed, convex, bounded below), III.b (no satiation on $X_i$) and III.c. Let $p^*$ be any price vector, $y_j^*$ any production plans and $x_i^*$ consumption vectors such that Condition 2 holds: each $x_i^*$ maximizes $u_i$ over $\{x_i \in X_i : p^*\cdot x_i \leqq p^*\cdot\zeta_i + \sum_j \alpha_{ij}\, p^*\cdot y_j^*\}$. Then every consumer spends the whole income:
--   $$p^*\cdot x_i^* = p^*\cdot\zeta_i + \sum_{j=1}^n \alpha_{ij}\, p^*\cdot y_j^* \qquad (i = 1, \dots, m).$$
--
--   Summed over consumers, this identity gives the equality $p^*\cdot z^* = 0$ of Condition 4.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 272 (PDF p. 9), §1.4.2, display (1)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§1.4.2, display (1)**, Arrow & Debreu, Econometrica 22 (1954), p. 272 (PDF p. 9): each
individual spends his entire potential income — if Condition 2 holds at `(p^*, x^*, y^*)`, then
for every consumer `i`,
`p^*·x_i^* = p^*·ζ_i + Σ_j α_{ij} p^*·y_j^*`.

**Formalization Note.** The paragraph uses Condition 2, III.b, III.c and the convexity of `X_i`
(the point `t x_i' + (1 − t) x_i^*` must lie in `X_i`); Assumption II supplies the convexity.
Nothing is assumed about `p^*` (not even Condition 3): the argument does not use it. -/
theorem budget_exhausted {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E)
    (hIIIb : AssumptionIIIb E) (hIIIc : AssumptionIIIc E)
    (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ)
    (h2 : Condition2 E p x y) :
    ∀ i, p ⬝ᵥ x i = income E p y i := by sorry

end ArrowDebreu.ThmI
