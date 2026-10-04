-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_prop_2_24_circuit_parallel_series_support
-- name    : DiscreteConvex.CombinatorialC.prop_2_24_circuit_parallel_series_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:24.149708+00:00
-- url     : https://prove2.me/theorems/69f6f2b9-cda5-4679-a9fe-1363fc0e80c8
-- title:
--   Proposition 2.24 -- a circuit meets a parallel/series arc set sparsely
-- statement:
--   For a circuit $\pi$: $|\operatorname{supp}^+(\pi)\cap P|\le1$, $|\operatorname{supp}^-(\pi)\cap P|\le1$ for parallel $P$; $\operatorname{supp}^+(\pi)\cap S=\emptyset$ or $\operatorname{supp}^-(\pi)\cap S=\emptyset$ for series $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, Proposition 2.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, Proposition 2.24

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.84, Proposition 2.24, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.24.** Let `π` be a circuit. (1) `|supp⁺(π) ∩ P| ≤ 1` and
`|supp⁻(π) ∩ P| ≤ 1` for a parallel arc set `P`. (2) `|supp⁺(π) ∩ S| = 0` or
`|supp⁻(π) ∩ S| = 0` for a series arc set `S`. -/
theorem prop_2_24_circuit_parallel_series_support {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (pi : A → ℝ)
    (hpi : IsCircuit src dst pi) (P S : Finset A) (hP : IsParallelArcSet src dst P)
    (hS : IsSeriesArcSet src dst S) :
    ((SuppPosR pi ∩ P).card ≤ 1 ∧ (SuppNegR pi ∩ P).card ≤ 1) ∧
      ((SuppPosR pi ∩ S) = ∅ ∨ (SuppNegR pi ∩ S) = ∅) := by sorry

end DiscreteConvex.CombinatorialC
