-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_Etilde_has_equilibrium
-- name    : ArrowDebreu.ThmI.Etilde_has_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:43:20.590244+00:00
-- url     : https://prove2.me/theorems/eff4c490-4d50-4827-8944-f0f8a35e685c
-- title:
--   The truncated abstract economy $\tilde E$ has an equilibrium point (§3.4.0)
-- statement:
--   Let an economy with $l \ge 1$ commodities satisfy Assumptions I–IV. Let $c > 0$ be such that the cube $C = \{x : |x_h| \le c \text{ for all } h\}$ contains every attainable set $\hat X_i$ and $\hat Y_j$ in its interior, and let $\tilde E$ be the truncated abstract economy of §3.3.4 ($E$ with $X_i$ replaced by $X_i \cap C$ and $Y_j$ by $Y_j \cap C$). Then $\tilde E$ has an equilibrium point
--   $$(x_1^*, \dots, x_m^*, y_1^*, \dots, y_n^*, p^*).$$
--
--   This is the step at which the equilibrium-existence lemma is applied; all of its hypotheses are checked for $\tilde E$ in §3.3.4–§3.3.5.
--
--   **Formalization Note** $l \ge 1$ is required: for $l = 0$ the price simplex is empty and no equilibrium point can exist.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 279 (PDF p. 16), §3.4.0 (c chosen in §3.3.3, p. 277)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.4.0**, Arrow & Debreu, Econometrica 22 (1954), p. 279 (PDF p. 16): "The existence of an
equilibrium point `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` for the abstract economy `Ẽ` has,
therefore, been demonstrated."

For an economy with `l ≥ 1` commodities satisfying Assumptions I–IV, and a positive real `c`
chosen as in §3.3.3 (the cube `C = {x | |x_h| ≦ c for all h}` contains in its interior all `X̂_i`
and all `Ŷ_j`), the truncated abstract economy `Ẽ` of §3.3.4 has an equilibrium point.

**Formalization Note.** `0 < l` is needed: for `l = 0` the price simplex `P` is empty and no
abstract economy containing the market participant has an equilibrium point. "Interior" is the
topological interior in `R^l`. -/
theorem Etilde_has_equilibrium {l m n : ℕ} (hl : 0 < l) (E : Economy l m n)
    (hE : AssumptionsItoIV E) (c : ℝ) (hc : 0 < c)
    (hX : ∀ i, Xhat E i ⊆ interior (cube l c)) (hY : ∀ j, Yhat E j ⊆ interior (cube l c)) :
    ∃ a, (economyEtilde E c).IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmI
