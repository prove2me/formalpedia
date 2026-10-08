-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_fact1
-- name    : BesbesZeevi.Parametric.fact1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:02:31.130169+00:00
-- url     : https://prove2.me/theorems/b5805f5e-63ef-4d8f-a681-2262d68c9280
-- title:
--   Fact 1 — scaling and positive deterministic benchmark
-- statement:
--   For every parameter $\theta\in\Theta$ and positive integer market size $n$, scaling both demand and inventory by $n$ scales the deterministic benchmark by $n$. The unscaled benchmark also has a uniform positive value:
--
--   $$J_n^D(x,T\mid\theta)=nJ^D(x,T\mid\theta),\qquad J^D(x,T\mid\theta)\ge m\min\{T,x/M\}>0.$$
--
--   The bound makes the regret ratio well-defined uniformly over the family. The constants $m$ and $M$ are the common Assumption 1 bounds.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF p. 29), Fact 1

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Model

namespace BesbesZeevi.Parametric

/-- Fact 1, p. 27: scaling and a uniform positive lower bound for the benchmark. -/
theorem fact1 {k : ℕ} (D : Market) (F : Family k D) :
    (∀ θ ∈ F.Θ, ∀ n : ℕ, 1 ≤ n →
      jDetScaled D F θ n = (n : ℝ) * jDet D (fun p => F.demand p θ) D.x) ∧
    (∀ θ ∈ F.Θ,
      D.m * min D.T (D.x / D.M) ≤ jDet D (fun p => F.demand p θ) D.x) := by sorry

end BesbesZeevi.Parametric
