-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_budget_slack_on_Peps
-- name    : ArrowDebreu.ThmII.budget_slack_on_Peps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:16:45.90122+00:00
-- url     : https://prove2.me/theorems/619c2491-8b9b-4c90-ab9b-d83af286c880
-- title:
--   On $P^\varepsilon$ every consumer can spend strictly less than the value of the endowment
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII, and let $\pi$ be the number of types of productive labor. Let $0<\varepsilon\le 1/(2\pi)$ and let $p\in P^\varepsilon$, a price vector in the simplex that gives every type of productive labor a price of at least $\varepsilon$. Then every consumer $i$ has a consumption vector costing strictly less than the endowment:
--   $$\exists\,x_i\in X_i:\qquad p\cdot x_i<p\cdot\zeta_i.$$
--
--   This is what the floor $\varepsilon$ on labor prices buys: with it, the budget sets of $E^\varepsilon$ have nonempty interior relative to $X_i$, which is the hypothesis under which the budget correspondence is continuous.
--
--   **Formalization Note** Assumption V is not assumed; the paper uses it only in §5.3.5.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 282 (PDF p. 19), §5.0, display (1)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **§5.0 (1)** (Arrow & Debreu, Econometrica 22 (1954), display (1) of §5.0, p. 282,
PDF p. 19). For an economic system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed), for every `ε` with
`0 < ε ≦ 1/(2π)` (`π` the number of elements of `𝒫`) and every price vector `p ∈ P^ε`, every
consumer `i` can afford a point strictly inside the budget: for some `x_i ∈ X_i`, `p·x_i < p·ζ_i`.

**Formalization Note.** `π = (productive E).card`; the scan prints the upper bound on `ε` as
"½π", which the proof on p. 283 (`2πε ≦ 1`) shows to be `1/(2π)`. -/
theorem budget_slack_on_Peps {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (p : Fin l → ℝ) (hp : p ∈ priceSimplexEps E ε) (i : Fin m) :
    ∃ x ∈ E.X i, p ⬝ᵥ x < p ⬝ᵥ E.ζ i := by sorry

end ArrowDebreu.ThmII
