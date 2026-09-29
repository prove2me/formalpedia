-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_condition2_at_E_equilibrium
-- name    : ArrowDebreu.ThmI.condition2_at_E_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:40:10.254698+00:00
-- url     : https://prove2.me/theorems/00be5f8d-13d1-448a-9dc6-2308eef26b7b
-- title:
--   At an equilibrium point of $E$ Condition 2 holds (§3.1.2 (2))
-- statement:
--   Let an economy satisfy Assumption I.a (each $Y_j$ is closed, convex and contains $0$) and Assumption IV.b ($\alpha_{ij} \ge 0$, $\sum_i \alpha_{ij} = 1$). Let $E$ be the abstract economy of §3.1.0, in which consumer $i$ faces the modified budget
--   $$p\cdot x_i \leqq p\cdot\zeta_i + \max\Big[0, \sum_j \alpha_{ij}\, p\cdot y_j\Big].$$
--   If $(x_1^*, \dots, x_m^*, y_1^*, \dots, y_n^*, p^*)$ is an equilibrium point of $E$, then Condition 2 holds: each $x_i^*$ maximizes $u_i$ over $\{x_i \in X_i : p^*\cdot x_i \leqq p^*\cdot\zeta_i + \sum_j \alpha_{ij}\, p^*\cdot y_j^*\}$.
--
--   The truncation $\max[0, \cdot]$ was introduced to keep every budget set nonempty; this statement says it is inactive at equilibrium.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 275 (PDF p. 12), §3.1.2, display (2)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.1.2, display (2)**, Arrow & Debreu, Econometrica 22 (1954), p. 275 (PDF p. 12):
"Condition 2 is satisfied at an equilibrium point of the abstract economy E."

Here `E = economyE E E.X E.Y` is the abstract economy of §3.1.0, whose consumers face the
budget `p·x_i ≦ p·ζ_i + max[0, Σ_j α_{ij} p·y_j]`; the claim is that at an equilibrium point
`a^*` the consumption vectors `x_i^*` satisfy Condition 2 at the prices `p^*` and production
plans `y_j^*` of `a^*`.

**Formalization Note.** The paragraph uses Assumption I.a (`0 ∈ Y_j`) and Assumption IV.b
(`α_{ij} ≧ 0`); these are the hypotheses. -/
theorem condition2_at_E_equilibrium {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E)
    (hIVb : AssumptionIVb E) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    Condition2 E (priceOf a) (consOf a) (prodOf a) := by sorry

end ArrowDebreu.ThmI
