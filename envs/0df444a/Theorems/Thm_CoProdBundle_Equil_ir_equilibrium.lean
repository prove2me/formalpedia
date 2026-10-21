-- Prove2me | Theorems.Thm_CoProdBundle_Equil_ir_equilibrium
-- name    : CoProdBundle.Equil.ir_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:40.627735+00:00
-- url     : https://prove2.me/theorems/fe0ed00d-6fdb-4207-81f3-89a7da6ed155
-- title:
--   §3.3, p. 11 — in equilibrium, producers with cost above γS(Q)/Q have no output and the others produce
-- statement:
--   Under the standing assumptions ($I \ge 1$ producers with costs $0 < c_1 \le \dots \le c_I$, $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$), let $(Q_1,\dots,Q_I)$ be a Nash equilibrium of the producers' game with positive aggregate output $Q = \sum_j Q_j > 0$. Then for every producer $i$,
--   $$Q_i > 0 \iff c_i < \frac{\gamma\,S(Q)}{Q}.$$
--
--   This is the individual-rationality sentence of §3.3: producers whose cost exceeds the average revenue $\gamma S(Q)/Q$ stay out, and the others are active.
--
--   **Formalization Note** The paper writes the threshold with a weak inequality ("cost parameter higher than $\gamma S(Q)/Q$ have no output"). At equality the producer's best response is $0$, so the exact statement is the strict one used here. Lean's producer `i` is the paper's producer $i+1$.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §3.3, p. 11 (with (4e), p. 16)

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- §3.3, p. 11: in an equilibrium with positive aggregate output, a producer is active iff its
unit cost is below the average revenue `γ S(Q)/Q`. -/
theorem ir_equilibrium (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (q : Fin I → ℝ) (hq : IsNashEq γ A b w θ c q) (hQ : 0 < total q) (i : Fin I) :
    0 < q i ↔ c i < γ * S A b w θ (total q) / total q := by sorry

end CoProdBundle.Equil
