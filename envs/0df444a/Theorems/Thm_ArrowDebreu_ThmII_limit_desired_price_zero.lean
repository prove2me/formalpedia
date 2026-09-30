-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_limit_desired_price_zero
-- name    : ArrowDebreu.ThmII.limit_desired_price_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:29:44.681768+00:00
-- url     : https://prove2.me/theorems/93514055-3819-4500-baef-11996c316e1d
-- title:
--   If the labor price floors bind, some always-desired commodity has limit price zero
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII. Let $\varepsilon_k\to0$ with $0<\varepsilon_k\le1/(2\pi)$, let $(x^k,y^k,p^k)$ be an equilibrium point of $E^{\varepsilon_k}$ with
--   $$p_h^k=\varepsilon_k\quad\text{for at least one }h\in\mathcal P,$$
--   for each $k$, and suppose $(x^k,y^k,p^k)\to(x^0,y^0,p^0)$. Then
--   $$p^0_{h'}=0\quad\text{for at least one }h'\in\mathcal D.$$
--
--   If the labor price floor keeps binding as $\varepsilon\to0$, some type of productive labor has limit price zero. Assumption VII then transmits the zero price to a desired commodity.
--
--   **Formalization Note** The hypothesis on $p^k$ is the case assumption of §5.3.1 (1), under which the paper argues by contradiction. Assumption V is not assumed; with it, the paper shows this situation cannot occur.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 285–286 (PDF pp. 22–23), §5.3.1 (1)–(2) and §5.3.4, display (3)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open Filter Topology

namespace ArrowDebreu.ThmII

/-- **§5.3.4 (3)** (Arrow & Debreu, Econometrica 22 (1954), display (3) of §5.3.4, p. 286,
PDF p. 23). For an economic system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed), let `ε_k → 0` with
`0 < ε_k ≦ 1/(2π)`, let `(x^k, y^k, p^k)` be an equilibrium point of `E^{ε_k}` with (§5.3.1 (1))
`p_h^k = ε_k` for at least one `h ∈ 𝒫`, and let `(x^k, y^k, p^k) → (x^0, y^0, p^0)` (§5.3.1 (2)).
Then `p^0_{h'} = 0` for at least one `h' ∈ 𝒟`.

**Formalization Note.** The limit point of §5.3.1 (2) is encoded by its construction: a sequence
`ε_k` in `(0, 1/(2π)]` tending to `0`, equilibrium points `a^k = (x^k, y^k, p^k)` of `E^{ε_k}`, and
`a^k → a^0 = (x^0, y^0, p^0)` coordinatewise (the product topology on profiles). The hypothesis `hbind` is §5.3.1 (1), the case assumption under which §5.3 argues (that
(1) of §5.3.0 fails for every `ε`). -/
theorem limit_desired_price_zero {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k ∧ εs k ≤ 1 / (2 * ((productive E).card : ℝ)))
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0))
    (hbind : ∀ k, ∃ h ∈ productive E, priceOf (as k) h = εs k) :
    ∃ h' ∈ desired E, priceOf a0 h' = 0 := by sorry

end ArrowDebreu.ThmII
