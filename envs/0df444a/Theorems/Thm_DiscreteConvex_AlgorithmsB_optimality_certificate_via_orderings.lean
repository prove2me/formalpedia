-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_optimality_certificate_via_orderings
-- name    : DiscreteConvex.AlgorithmsB.optimality_certificate_via_orderings
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T04:10:27.659989+00:00
-- url     : https://prove2.me/theorems/c7faa69f-4d4f-424a-8a45-6bb2b55a59f0
-- title:
--   Proposition 10.9 -- optimality_certificate_via_orderings
-- statement:
--   **Proposition 10.9** (p.289). A sufficient condition for optimality in (10.11), given a base $x$ represented as a convex combination of extreme bases $\{(L_i,\lambda_i)\mid i\in I\}$ and a subset $W$: (1) if the negative/positive supports of $x$ split along $W$, then $x^-(V)=x(W)$; (2) if every element of $W$ precedes every element outside $W$ in every $L_i$, then $x(W)=\rho(W)$; (3) under both conditions, $x$ and $W$ are optimal in (10.11).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Proposition 10.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Proposition 10.9

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPosR
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNegR
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrecedesIn
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.9 (p.289). A sufficient condition for optimality in (10.11), stated in terms
of the linear orderings representing a base as a convex combination of extreme bases. -/
theorem optimality_certificate_via_orderings {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (W : Finset V) :
    ((∀ v ∈ SuppNegR' x, v ∈ W) ∧ (∀ v ∈ SuppPosR' x, v ∉ W) →
      ∑ v, NegPart x v = ∑ v ∈ W, x v) ∧
    ((∀ i ∈ I, ∀ u ∈ W, ∀ v ∉ W, PrecedesIn (L i) u v) → ∑ v ∈ W, x v = (rho W : ℝ)) ∧
    (((∀ v ∈ SuppNegR' x, v ∈ W) ∧ (∀ v ∈ SuppPosR' x, v ∉ W)) →
      (∀ i ∈ I, ∀ u ∈ W, ∀ v ∉ W, PrecedesIn (L i) u v) →
      ∑ v, NegPart x v = (MinRho rho : ℝ) ∧ (rho W : ℤ) = MinRho rho) := by sorry

end DiscreteConvex.AlgorithmsB
