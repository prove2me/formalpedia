-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_base_polyhedron_support_function
-- name    : DiscreteConvex.MConvexSetsB.base_polyhedron_support_function
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:33:11.361131+00:00
-- url     : https://prove2.me/theorems/f41de2ae-9cf5-4797-b5b7-e6130fc1fbde
-- title:
--   Proposition 4.5 -- base_polyhedron_support_function
-- statement:
--   **Proposition 4.5** (p.105), Eq. (4.14). For a submodular set function $\rho \in S[\mathbb R]$,
--
--   $$\sup\{\langle p,x\rangle : x \in B(\rho)\} = \hat\rho(p) \qquad (p \in \mathbb R^V),$$
--
--   where $\hat\rho$ is the Lovász extension of $\rho$ (Eq. (4.6)): the support function of the base polyhedron coincides exactly with the Lovász extension.
--
--   **Formalization Note.** The supremum is taken in `WithTop ℝ` (via `iSup`), which is `⊤` exactly when the linear program is unbounded — matching the possibly-infinite values the Lovász extension itself takes.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, Proposition 4.5, Eq. (4.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, Proposition 4.5

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.105, Proposition 4.5, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.5 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.105). See the item's
`natural_language_statement` for the full statement. -/
theorem base_polyhedron_support_function {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (p : V → ℝ) :
    (⨆ x ∈ BasePolyhedron ρ, (((∑ v, p v * x v : ℝ)) : WithTop ℝ)) = LovaszExtension ρ p := by sorry

end DiscreteConvex.MConvexSetsB
