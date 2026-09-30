-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_EtildeEps_has_equilibrium
-- name    : ArrowDebreu.ThmII.EtildeEps_has_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:22:14.114971+00:00
-- url     : https://prove2.me/theorems/8555e1c9-92b3-4972-a983-429df99b2c76
-- title:
--   The truncated economy $\tilde E^\varepsilon$ has an equilibrium point
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII, lower bounds $\xi_i$ of the consumption sets, and a positive real $c'$ such that the cube $C'=\{x:|x_h|\le c'\ \forall h\}$ contains every $\hat X'_i$ and every $\hat Y'_j$ in its interior. Then for each $\varepsilon$ with
--   $$0<\varepsilon\le\frac1{2\pi},$$
--   the truncated abstract economy $\tilde E^\varepsilon$ has an equilibrium point $(x_1^*,\dots,x_m^*,y_1^*,\dots,y_n^*,p^*)$.
--
--   This is the step at which the existence lemma for abstract economies (Debreu 1952) is applied; the truncation makes all action sets compact.
--
--   **Formalization Note** "Contains in its interior" is inclusion in the topological interior of $C'$. Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 284 (PDF p. 21), §5.2.1

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **§5.2.1** (Arrow & Debreu, Econometrica 22 (1954), §5.2.1, p. 284, PDF p. 21). For an economic
system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed), lower bounds `ξ_i` as in Assumption II, and a
positive real `c'` such that the cube `C' = {x | |x_h| ≦ c' for all h}` contains in its interior
all `X̂'_i` and all `Ŷ'_j` (the choice of §5.2.0), the truncated abstract economy `Ẽ^ε` has an
equilibrium point `[x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*]` for each `ε`, `0 < ε ≦ 1/(2π)`.

**Formalization Note.** `Ẽ^ε = economyEtildeEps E ε c'` is `E^ε` with `X_i` replaced by
`X_i ∩ C'` and `Y_j` by `Y_j ∩ C'` everywhere. "Contains in its interior" is `⊆ interior C'`
(Mathlib's topological interior in `Fin l → ℝ`). -/
theorem EtildeEps_has_equilibrium {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (c' : ℝ) (hc' : 0 < c')
    (hX : ∀ i, XhatPrime E ξ i ⊆ interior (cube l c'))
    (hY : ∀ j, YhatPrime E ξ j ⊆ interior (cube l c'))
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ))) :
    ∃ a : Player m n → Fin l → ℝ, (economyEtildeEps E ε c').IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmII
