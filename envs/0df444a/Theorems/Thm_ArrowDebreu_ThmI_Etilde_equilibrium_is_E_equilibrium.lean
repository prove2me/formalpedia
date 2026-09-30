-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_Etilde_equilibrium_is_E_equilibrium
-- name    : ArrowDebreu.ThmI.Etilde_equilibrium_is_E_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:43:50.422044+00:00
-- url     : https://prove2.me/theorems/2074577c-c0e0-42f6-94de-1a9104b32323
-- title:
--   An equilibrium point of $\tilde E$ is an equilibrium point of $E$ (§3.4.1)
-- statement:
--   Let an economy satisfy Assumptions I–IV, let $c > 0$ be such that the cube $C = \{x : |x_h| \le c \text{ for all } h\}$ contains every attainable set $\hat X_i$ and $\hat Y_j$ in its interior, and let $\tilde E$ and $E$ be the truncated and untruncated abstract economies of §3.3.4 and §3.1.0. Then every equilibrium point
--   $$(x_1^*, \dots, x_m^*, y_1^*, \dots, y_n^*, p^*)$$
--   of $\tilde E$ is also an equilibrium point of $E$.
--
--   Combined with the statement that equilibrium points of $E$ are competitive equilibria (§3.2), this completes the proof of Theorem I.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 279 (PDF p. 16), §3.4.1

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.4.1**, Arrow & Debreu, Econometrica 22 (1954), p. 279 (PDF p. 16): "It has been shown,
therefore, that the point `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` is also an equilibrium point
for E".

For an economy satisfying Assumptions I–IV and a positive real `c` chosen as in §3.3.3 (the cube
`C` contains in its interior all `X̂_i` and all `Ŷ_j`), every equilibrium point of the truncated
abstract economy `Ẽ` of §3.3.4 is an equilibrium point of the abstract economy `E` of §3.1.0.

**Formalization Note.** The second half of the paper's sentence ("as shown in 3.2., it is,
therefore, a competitive equilibrium") is the item `E_equilibrium_is_competitive`. -/
theorem Etilde_equilibrium_is_E_equilibrium {l m n : ℕ} (E : Economy l m n)
    (hE : AssumptionsItoIV E) (c : ℝ) (hc : 0 < c)
    (hX : ∀ i, Xhat E i ⊆ interior (cube l c)) (hY : ∀ j, Yhat E j ⊆ interior (cube l c))
    (a : Player m n → Fin l → ℝ) (ha : (economyEtilde E c).IsEquilibriumPoint a) :
    (economyE E E.X E.Y).IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmI
