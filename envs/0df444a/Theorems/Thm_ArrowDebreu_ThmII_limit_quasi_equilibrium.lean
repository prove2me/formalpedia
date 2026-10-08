-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_limit_quasi_equilibrium
-- name    : ArrowDebreu.ThmII.limit_quasi_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:27:49.809554+00:00
-- url     : https://prove2.me/theorems/e958708d-037e-44b3-a4b4-6421f59b53cb
-- title:
--   The limit of equilibrium points of $E^{\varepsilon_k}$ is a quasi-equilibrium for consumers
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII. Let $\varepsilon_k\to0$ with $0<\varepsilon_k\le1/(2\pi)$, let $(x^k,y^k,p^k)=(x_1^k,\dots,x_m^k,y_1^k,\dots,y_n^k,p^k)$ be an equilibrium point of $E^{\varepsilon_k}$ for each $k$, and suppose $x_i^k\to x_i^0$, $y_j^k\to y_j^0$, $p^k\to p^0$. Then for every consumer $i$ and every $x_i\in X_i$,
--   $$u_i(x_i)>u_i(x_i^0)\ \Longrightarrow\ p^0\cdot x_i\ge p^0\cdot x_i^0.$$
--
--   Anything strictly preferred to the limit consumption costs at least as much at the limit prices. This is the quasi-equilibrium property, weaker than utility maximization under the budget.
--
--   **Formalization Note** The limit point of §5.3.1 (2) is encoded by its construction: a sequence of equilibrium points converging coordinatewise. Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 285 (PDF p. 22), §5.3.1 (2) and §5.3.2, display (1)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open Filter Topology

namespace ArrowDebreu.ThmII

/-- **§5.3.2 (1)** (Arrow & Debreu, Econometrica 22 (1954), display (1) of §5.3.2, p. 285,
PDF p. 22). For an economic system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed), let `ε_k → 0` with
`0 < ε_k ≦ 1/(2π)`, let `(x_1^k, ⋯, x_m^k, y_1^k, ⋯, y_n^k, p^k)` be an equilibrium point of `E^{ε_k}`,
and let `x_i^k → x_i^0`, `y_j^k → y_j^0`, `p^k → p^0` (§5.3.1 (2)). Then for every consumer `i`:
if `x_i ∈ X_i` and `u_i(x_i) > u_i(x_i^0)`, then `p^0·x_i ≧ p^0·x_i^0`.

**Formalization Note.** The limit point of §5.3.1 (2) is encoded by its construction: a sequence
`ε_k` in `(0, 1/(2π)]` tending to `0`, equilibrium points `a^k = (x^k, y^k, p^k)` of `E^{ε_k}`, and
`a^k → a^0 = (x^0, y^0, p^0)` coordinatewise (the product topology on profiles). -/
theorem limit_quasi_equilibrium {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k ∧ εs k ≤ 1 / (2 * ((productive E).card : ℝ)))
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) :
    ∀ i, ∀ x ∈ E.X i, E.u i (consOf a0 i) < E.u i x →
      priceOf a0 ⬝ᵥ consOf a0 i ≤ priceOf a0 ⬝ᵥ x := by sorry

end ArrowDebreu.ThmII
