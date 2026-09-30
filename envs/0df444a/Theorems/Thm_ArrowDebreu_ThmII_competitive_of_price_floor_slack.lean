-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_competitive_of_price_floor_slack
-- name    : ArrowDebreu.ThmII.competitive_of_price_floor_slack
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:26:01.024363+00:00
-- url     : https://prove2.me/theorems/3b6b90f3-71f8-4ab1-b73d-370bc19516d2
-- title:
--   If the labor price floor is slack, the equilibrium point of $E^\varepsilon$ is a competitive equilibrium
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII, and $\varepsilon$ with $0<\varepsilon\le1/(2\pi)$. Let $(x_1^*,\dots,x_m^*,y_1^*,\dots,y_n^*,p^*)$ be an equilibrium point of $E^\varepsilon$ such that
--   $$p_h^*>\varepsilon\quad\text{for all }h\in\mathcal P.$$
--   Then $(x_1^*,\dots,x_m^*,y_1^*,\dots,y_n^*,p^*)$ is a competitive equilibrium: it satisfies Conditions 1–4.
--
--   The contraction of the price domain to $P^\varepsilon$ is harmless as soon as the floor does not bind. The rest of the proof shows that for some $\varepsilon$ it does not.
--
--   **Formalization Note** The paper states the conclusion as "there is a competitive equilibrium". Its proof shows that this very point is one, and that is what is stated. Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 284–285 (PDF pp. 21–22), §5.3.0, displays (1) and (2)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **§5.3.0 (2)** (Arrow & Debreu, Econometrica 22 (1954), displays (1)–(2) of §5.3.0,
pp. 284–285, PDF pp. 21–22). For an economic system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed),
suppose that for some `ε`, `0 < ε ≦ 1/(2π)`, an equilibrium point `[x^*, y^*, p^*]` of `E^ε`
satisfies (1) `p_h^* > ε` for all `h ∈ 𝒫`. Then `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` is a
competitive equilibrium (Conditions 1–4): "(2) If (1) holds, there is a competitive equilibrium."

**Formalization Note.** The paper's proof shows that this very point is a competitive equilibrium;
that is what is stated (it implies the existential "there is"). -/
theorem competitive_of_price_floor_slack {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (a : Player m n → Fin l → ℝ) (ha : (economyEeps E ε).IsEquilibriumPoint a)
    (hslack : ∀ h ∈ productive E, ε < priceOf a h) :
    IsCompetitiveEquilibrium E (consOf a) (prodOf a) (priceOf a) := by sorry

end ArrowDebreu.ThmII
