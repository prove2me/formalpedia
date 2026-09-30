-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_limit_expenditure_minimization
-- name    : ArrowDebreu.ThmII.limit_expenditure_minimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:31:55.397949+00:00
-- url     : https://prove2.me/theorems/8d48d23f-3172-45ae-ae54-c6fa51bef590
-- title:
--   If the labor price floors bind, every limit consumption minimizes expenditure
-- statement:
--   Under the hypotheses of the previous statement (Assumptions I–III, IV′, VI and VII; $\varepsilon_k\to0$; equilibrium points of $E^{\varepsilon_k}$ with $p_h^k=\varepsilon_k$ for some $h\in\mathcal P$, converging to $(x^0,y^0,p^0)$), every consumer's limit consumption minimizes expenditure: $x_i^0\in X_i$ and
--   $$p^0\cdot x_i^0\le p^0\cdot x_i\quad\text{for all }x_i\in X_i.$$
--
--   Since some always-desired good is free at $p^0$, the quasi-equilibrium property strengthens to cost minimization over the whole consumption set. Summing over consumers, $x^0$ minimizes $p^0\cdot x$ over $X$, and this contradicts Assumption V.
--
--   **Formalization Note** Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 286–287 (PDF pp. 23–24), §5.3.4, display (6)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open Filter Topology

namespace ArrowDebreu.ThmII

/-- **§5.3.4 (6)** (Arrow & Debreu, Econometrica 22 (1954), display (6) of §5.3.4, p. 287,
PDF p. 24). For an economic system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed), let `ε_k → 0` with
`0 < ε_k ≦ 1/(2π)`, let `(x^k, y^k, p^k)` be an equilibrium point of `E^{ε_k}` with (§5.3.1 (1))
`p_h^k = ε_k` for at least one `h ∈ 𝒫`, and let `(x^k, y^k, p^k) → (x^0, y^0, p^0)` (§5.3.1 (2)).
Then for every consumer `i`, `x_i^0` minimizes `p^0·x_i` over `X_i`: `x_i^0 ∈ X_i` and
`p^0·x_i^0 ≦ p^0·x_i` for all `x_i ∈ X_i`.

**Formalization Note.** The limit point of §5.3.1 (2) is encoded by its construction: a sequence
`ε_k` in `(0, 1/(2π)]` tending to `0`, equilibrium points `a^k = (x^k, y^k, p^k)` of `E^{ε_k}`, and
`a^k → a^0 = (x^0, y^0, p^0)` coordinatewise (the product topology on profiles). The hypothesis `hbind` is §5.3.1 (1). -/
theorem limit_expenditure_minimization {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k ∧ εs k ≤ 1 / (2 * ((productive E).card : ℝ)))
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0))
    (hbind : ∀ k, ∃ h ∈ productive E, priceOf (as k) h = εs k) :
    ∀ i, consOf a0 i ∈ E.X i ∧ ∀ x ∈ E.X i, priceOf a0 ⬝ᵥ consOf a0 i ≤ priceOf a0 ⬝ᵥ x := by sorry

end ArrowDebreu.ThmII
