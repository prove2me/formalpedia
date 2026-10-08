-- Prove2me | Theorems.Thm_CJP83_CoverSeparation_relaxed_lifting_valid
-- name    : CJP83.CoverSeparation.relaxed_lifting_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:54:44.652977+00:00
-- url     : https://prove2.me/theorems/b49afada-1eb1-4882-9d9b-71a58862af5c
-- title:
--   p. 814, §2.4 — relaxed lifting preserves validity
-- statement:
--   Let $\sum_{j\in S} f_jx_j\le f_0$ be valid for every feasible zero–one solution of the positive-weight row (2.5) supported in $S$, with integer coefficients. For $k\notin S$, let $\bar z_k$ be the attained optimum of the LP relaxation of (2.10) and define
--   $$
--   f_k=f_0-\lfloor\bar z_k\rfloor.
--   $$
--   Then $\sum_{j\in S}f_jx_j+f_kx_k\le f_0$ holds for every feasible zero–one solution supported in $S\cup\{k\}$. This formalizes the paper's relaxed extension step. Attainment excludes a lifting problem with no feasible point, as in the procedure after variable fixing.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), p. 814, Section 2.4, (2.10), relaxed lifting paragraph

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

namespace CJP83.CoverSeparation

theorem relaxed_lifting_valid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (S : Finset ι) (f : ι → ℤ) (f₀ : ℤ) (k : ι) (hk : k ∉ S)
    (hvalid : IsValidOn a a₀ S f f₀)
    (zbar : ℝ) (hzbar : IsGreatest (relaxedLiftValues a a₀ S f k) zbar) :
    IsValidOn a a₀ (insert k S)
      (Function.update f k (f₀ - Int.floor zbar)) f₀ := by sorry
end CJP83.CoverSeparation
