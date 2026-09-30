-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_eqPoint_EtildeEps_is_eqPoint_Eeps
-- name    : ArrowDebreu.ThmII.eqPoint_EtildeEps_is_eqPoint_Eeps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:24:16.006181+00:00
-- url     : https://prove2.me/theorems/05661638-d144-4660-b3be-c26ac2555cae
-- title:
--   An equilibrium point of $\tilde E^\varepsilon$ is an equilibrium point of $E^\varepsilon$
-- statement:
--   Under the hypotheses of the previous statement (Assumptions I–III, IV′, VI, VII; lower bounds $\xi_i$; a positive $c'$ whose cube contains every $\hat X'_i$ and $\hat Y'_j$ in its interior), let $0<\varepsilon\le1/(2\pi)$. Every equilibrium point of the truncated economy $\tilde E^\varepsilon$ is an equilibrium point of $E^\varepsilon$:
--
--   1. $x_i^*$ maximizes $u_i(x_i)$ for $x_i\in A_i(\bar x_i^*)$;
--   2. $y_j^*$ maximizes $p^*\cdot y_j$ for $y_j\in Y_j$;
--   3. $p^*$ maximizes $p\cdot z^*$ for $p\in P^\varepsilon$.
--
--   Removing the cube does not destroy equilibrium, because the equilibrium lies in the interior of the cube and the problems are convex.
--
--   **Formalization Note** The three items together are the definition of an equilibrium point of $E^\varepsilon$. Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 284 (PDF p. 21), §5.2.2, displays (3)–(5)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **§5.2.2 (3)–(5)** (Arrow & Debreu, Econometrica 22 (1954), displays (3), (4), (5) of §5.2.2,
p. 284, PDF p. 21). Under the hypotheses of §5.2.1 (Assumptions I–III, IV′, VI, VII — not V; lower bounds
`ξ_i`; a positive `c'` whose cube `C'` contains all `X̂'_i` and `Ŷ'_j` in its interior), for each
`ε`, `0 < ε ≦ 1/(2π)`, every equilibrium point of the truncated economy `Ẽ^ε` is an equilibrium
point of `E^ε`:
(3) `x_i^*` maximizes `u_i(x_i)` for `x_i ∈ A_i(x̄_i^*)`;
(4) `y_j^*` maximizes `p^*·y_j` for `y_j ∈ Y_j`;
(5) `p^*` maximizes `p·z^*` for `p ∈ P^ε`.

**Formalization Note.** The three displays together are the statement that the point is an
equilibrium point (Definition §2.3) of `E^ε = economyEeps E ε`. -/
theorem eqPoint_EtildeEps_is_eqPoint_Eeps {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (c' : ℝ) (hc' : 0 < c')
    (hX : ∀ i, XhatPrime E ξ i ⊆ interior (cube l c'))
    (hY : ∀ j, YhatPrime E ξ j ⊆ interior (cube l c'))
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (a : Player m n → Fin l → ℝ) (ha : (economyEtildeEps E ε c').IsEquilibriumPoint a) :
    (economyEeps E ε).IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmII
