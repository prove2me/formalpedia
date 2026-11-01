-- Prove2me | Theorems.Thm_AndOrSched_eq_3
-- name    : AndOrSched.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:07.345247+00:00
-- url     : https://prove2.me/theorems/ea5c5073-f91e-43b0-a8a4-06393b06f95e
-- title:
--   (3), p.8 — $\alpha C_b(\beta)\le t^\beta_b$
-- statement:
--   Let the instance have integer processing times $p_j\in\{0,1\}$, let $x$ be a feasible solution of LP (1), $0<\beta\le1$, $\alpha=\beta/\Delta$, and let $\prec$ be an order compatible with the keys $t^\alpha_a$ ($a\in A$), $t^\beta_b$ ($b\in B$). Then for every $b\in B$ the completion time $C_b(\beta)=\sum_{i\preceq b}p_i$ satisfies
--   $$\alpha\,C_b(\beta)\;\le\;t^\beta_b .$$
--
--   Differences from the source:
--   - generalization: x̄ optimal ("there is no idle time on the machine in the optimal fractional solution", Σ η p = t) → x any feasible solution, with only Σ η p ≤ t used; reason: the inequality follows from (1c) alone; optimal solutions are feasible
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, (3), p.8

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_key
open scoped Classical NNReal

namespace AndOrSched

/-- Display (3), p.8 (Happach, Schulz, arXiv:2001.07011v1): `α C_b(β) = Σ_{i⪯b} α pᵢ ≤ Σ_{i⪯b} η_i^b(β) pᵢ ≤ t_b^β`.

Let the instance have integer processing times at most `1`, let `x` be a feasible solution of
LP (1), `β ∈ (0, 1]`, `α = β/Δ`, and `σ` an order compatible with the keys of the `β`-schedule. Then
for every `b ∈ B` the completion time of `b` in the schedule of `σ` satisfies `α C_b ≤ t_b^β`. -/
theorem eq_3 (I : Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N)) (hσ : Compat I (key I x β) σ) (b : I.B) :
    β / (delta I : ℝ) * listC I σ (Sum.inr b) ≤ (alphaPoint x (Sum.inr b) β : ℝ) := by sorry

end AndOrSched
