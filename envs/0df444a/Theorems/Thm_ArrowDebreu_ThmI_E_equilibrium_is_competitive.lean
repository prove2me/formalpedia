-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_E_equilibrium_is_competitive
-- name    : ArrowDebreu.ThmI.E_equilibrium_is_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:41:11.147418+00:00
-- url     : https://prove2.me/theorems/c1950e26-b88b-4f66-a561-b5028d6fc6f7
-- title:
--   Every equilibrium point of $E$ is a competitive equilibrium (§3.2)
-- statement:
--   Let an economy satisfy Assumptions I–IV, and let $E$ be the abstract economy of §3.1.0 (consumers maximize $u_i$ under the budget $p\cdot x_i \leqq p\cdot\zeta_i + \max[0, \sum_j \alpha_{ij}\, p\cdot y_j]$, producers maximize $p\cdot y_j$ over $Y_j$, and a market participant maximizes $p\cdot z$ over the price simplex $P$). If $a^* = (x_1^*, \dots, x_m^*, y_1^*, \dots, y_n^*, p^*)$ is an equilibrium point of $E$, then
--   $$(x_1^*, \dots, x_m^*, y_1^*, \dots, y_n^*, p^*) \text{ satisfies Conditions 1–4},$$
--   i.e. it is a competitive equilibrium in the sense of Definition 1.5.0.
--
--   This reduces Theorem I to the existence of an equilibrium point of $E$.
--
--   **Formalization Note** Only this direction is stated; the converse, which the paper calls obvious, is not part of the item.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 275–276 (PDF pp. 12–13), §3.2

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.2**, Arrow & Debreu, Econometrica 22 (1954), pp. 275–276 (PDF pp. 12–13): "(1) and (2)
together assert Condition 4. It has been shown that any equilibrium point of E satisfies
Conditions 1–4 and hence is a competitive equilibrium."

For an economy satisfying Assumptions I–IV, if `a^*` is an equilibrium point of the abstract
economy `E` of §3.1.0, then its consumption vectors, production plans and price vector
`(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` form a competitive equilibrium (Definition 1.5.0).

**Formalization Note.** Only the forward direction is stated; the paper's "The converse is
obviously also true" is not part of this item. -/
theorem E_equilibrium_is_competitive {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsItoIV E)
    (a : Player m n → Fin l → ℝ) (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    IsCompetitiveEquilibrium E (consOf a) (prodOf a) (priceOf a) := by sorry

end ArrowDebreu.ThmI
