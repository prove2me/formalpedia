-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_eqPoint_Eeps_le_zetaPrime
-- name    : ArrowDebreu.ThmII.eqPoint_Eeps_le_zetaPrime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:18:31.390114+00:00
-- url     : https://prove2.me/theorems/32766e9e-943b-4e34-9d67-1432c949c0c6
-- title:
--   Equilibrium points of $E^\varepsilon$ satisfy $x^*-y^*\leqq\zeta'$
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII, lower bounds $\xi_i\leqq x_i$ ($x_i\in X_i$) of the consumption sets, and the vector $\zeta'$ built from them. For every $\varepsilon$ with $0<\varepsilon\le1/(2\pi)$ and every equilibrium point $(x_1^*,\dots,x_m^*,y_1^*,\dots,y_n^*,p^*)$ of the abstract economy $E^\varepsilon$,
--   $$x^*-y^*\leqq\zeta',\qquad x^*=\sum_ix_i^*,\ y^*=\sum_jy_j^*.$$
--
--   The bound $\zeta'$ does not depend on $\varepsilon$, so all equilibrium points of all the economies $E^\varepsilon$ lie in one bounded region. This lets a single cube $C'$ serve for every $\varepsilon$.
--
--   **Formalization Note** The inequality is componentwise. Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 283 (PDF p. 20), §5.1.1, display (5)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **§5.1.1 (5)** (Arrow & Debreu, Econometrica 22 (1954), display (5) of §5.1.1, p. 283,
PDF p. 20). For an economic system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed), let `ξ_i` be lower
bounds of the consumption sets as in Assumption II and `ζ'` the vector of §5.1.1. For every `ε` with
`0 < ε ≦ 1/(2π)` and every equilibrium point `[x^*, y^*, p^*]` of the abstract economy `E^ε`,
`x^* − y^* ≦ ζ'`, where `x^* = Σ_i x_i^*` and `y^* = Σ_j y_j^*`.

**Formalization Note.** `ζ' = zetaPrime E ξ` depends on the chosen lower bounds `ξ_i`, which enter
as a parameter together with the hypothesis `ξ_i ≦ x_i` on `X_i`. The inequality is componentwise
(Lean's `≤` on `Fin l → ℝ`). -/
theorem eqPoint_Eeps_le_zetaPrime {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (a : Player m n → Fin l → ℝ) (ha : (economyEeps E ε).IsEquilibriumPoint a) :
    ∑ i, consOf a i - ∑ j, prodOf a j ≤ zetaPrime E ξ := by sorry

end ArrowDebreu.ThmII
