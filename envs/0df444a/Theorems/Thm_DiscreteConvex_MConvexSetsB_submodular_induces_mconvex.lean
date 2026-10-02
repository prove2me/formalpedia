-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_submodular_induces_mconvex
-- name    : DiscreteConvex.MConvexSetsB.submodular_induces_mconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:25.234997+00:00
-- url     : https://prove2.me/theorems/9252665b-9a51-4eb0-9dbc-e5260ba2275e
-- title:
--   Proposition 4.14 -- submodular_induces_mconvex
-- statement:
--   **Proposition 4.14** (p.109-110), the converse of Proposition 4.13. Let $\rho \in S[\mathbb Z]$ be an integer-valued submodular set function. Then (1) $B = B(\rho) \cap \mathbb Z^V$ is an M-convex set, and (2) $\rho(X) = \sup\{x(X) : x \in B(\rho)\}$ for all $X \subseteq V$: the induced-function construction of Proposition 4.13 recovers $\rho$ itself when started from $B(\rho)\cap\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109-110, Proposition 4.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109-110, Proposition 4.14

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.109-110, Proposition 4.14, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.14 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.109-110). See the item's
`natural_language_statement` for the full statement. -/
theorem submodular_induces_mconvex {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hInt : IsIntegerValued ρ) :
    ExchangeAxiomB {x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ} ∧
      ({x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ}).Nonempty ∧
      (∀ X : Finset V, ρ X = ⨆ x ∈ BasePolyhedron ρ, (((∑ v ∈ X, x v : ℝ)) : WithTop ℝ)) := by sorry

end DiscreteConvex.MConvexSetsB
