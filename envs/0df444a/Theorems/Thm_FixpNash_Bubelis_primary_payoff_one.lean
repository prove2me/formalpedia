-- Prove2me | Theorems.Thm_FixpNash_Bubelis_primary_payoff_one
-- name    : FixpNash.Bubelis.primary_payoff_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:40.854631+00:00
-- url     : https://prove2.me/theorems/c85ad279-ef58-4f3c-9150-daf9f615a618
-- title:
--   Proof of Lemma 7, p. 26 — in every Nash equilibrium of $G_f$, $u_1((1:1); x_{-1}) = f(\xi)/\sum_{i=0}^m \xi^i$
-- statement:
--   Let $G_f$ be the gadget of Lemma 7 for coefficients $c_0, \dots, c_m$ and $f(x) = \sum_{j=0}^m c_j x^{m-j}$ (no hypothesis on $f$ is needed), let $x$ be a mixed Nash equilibrium of $G_f$ and $\xi = x_1(0)$. Then the expected payoff of the pure strategy $1$ of the primary player, against the strategies $x_2, x_3$ of the others, is
--   $$
--   u_1((1:1); x_{-1}) = \sum_{j=0}^m c_j\, x_2(j) = \frac{f(\xi)}{\sum_{i=0}^{m} \xi^{i}} .
--   $$
--
--   Since the pure strategy $0$ of player 1 always earns $0$, the sign of $f(\xi)$ decides which strategy the primary player prefers; this is what pins $\xi$ to a root of $f$.
--
--   **Formalization Note** $u_1((1:1); x_{-1})$ is `DGPNash.NashMap.purePayoff (gadget c) x primary 1`. The root hypotheses of Lemma 7 are not needed and are omitted.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 7, p. 26

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_Bubelis_Gadget

namespace FixpNash.Bubelis

open Finset

/-- Proof of Lemma 7, p. 26: in every Nash equilibrium `x` of the gadget `G_f`, writing
`ξ = x₁(0)`, the expected payoff of the pure strategy 1 of the primary player is
`u₁((1:1); x₋₁) = f(ξ) / ∑_{i=0}^m ξ^i`. -/
theorem primary_payoff_one {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) :
    DGPNash.NashMap.purePayoff (gadget c) x .primary 1 =
      poly c (x .primary 0) / ∑ i ∈ range (m + 1), x .primary 0 ^ i := by sorry

end FixpNash.Bubelis
