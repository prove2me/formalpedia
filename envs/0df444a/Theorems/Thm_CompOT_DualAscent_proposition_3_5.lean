-- Prove2me | Theorems.Thm_CompOT_DualAscent_proposition_3_5
-- name    : CompOT.DualAscent.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:30.234978+00:00
-- url     : https://prove2.me/theorems/f8bbbeba-5db8-4974-a188-724f2aceaa60
-- title:
--   Proposition 3.5, p. 415 — (f, g) + ε(1_S, −1_S′) stays dual feasible for small ε > 0 if S′ contains every balanced neighbour of S
-- statement:
--   Let $C \in \mathbb{R}^{n\times m}$ and let $(f,g) \in R(C)$ be dual feasible: $f_i + g_j \le C_{i,j}$ for all $i, j$. Call $(i,j')$ **balanced** if $f_i + g_j = C_{i,j}$. Let $S \subset [\![n]\!]$ and $S' \subset [\![m]\!]'$, and assume that for every $i \in S$, every balanced pair $(i,j')$ has $j' \in S'$. Then there is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon \le \varepsilon_0$ the perturbed pair
--   $$(\tilde f, \tilde g) = (f, g) + \varepsilon(\mathbb{1}_S, -\mathbb{1}_{S'})$$
--   is dual feasible, i.e. $\tilde f_i + \tilde g_j \le C_{i,j}$ for all $i, j$.
--
--   It describes which sparse $0/\pm1$ perturbations of a feasible dual pair keep it feasible; together with Proposition 3.6 it yields the ascent step of the primal-dual (Hungarian-type) method.
--
--   **Formalization Note** The book's "dual feasible for a small enough $\varepsilon > 0$" is stated in the stronger, equivalent form "for every $\varepsilon \in (0, \varepsilon_0]$" (the feasible set $R(C)$ is convex and contains $(f,g)$, so feasibility at one $\varepsilon$ implies it at every smaller one). $S$ and $S'$ are `Finset`s of `Fin n`, `Fin m`; $\mathbb 1_S$ is `indicatorVec S`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.5, p. 415

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

namespace CompOT.DualAscent

/-- Proposition 3.5, p. 415: if `(f, g)` is dual feasible and, for every `i ∈ S`, every pair
`(i, j')` balanced for `(f, g)` has `j' ∈ S'`, then `(f, g) + ε (𝟙_S, -𝟙_{S'})` is dual
feasible for every sufficiently small `ε > 0`. -/
theorem proposition_3_5 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hfg : CompOT.Duality.dualFeasible C f g) (S : Finset (Fin n)) (S' : Finset (Fin m))
    (hS : ∀ i ∈ S, ∀ j : Fin m, Balanced C f g i j → j ∈ S') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      CompOT.Duality.dualFeasible C (f + ε • indicatorVec S) (g - ε • indicatorVec S') := by sorry

end CompOT.DualAscent
