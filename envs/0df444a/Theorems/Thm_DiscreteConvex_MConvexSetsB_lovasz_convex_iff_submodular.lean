-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_lovasz_convex_iff_submodular
-- name    : DiscreteConvex.MConvexSetsB.lovasz_convex_iff_submodular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:33:27.3862+00:00
-- url     : https://prove2.me/theorems/a9735a4c-c06e-4dbc-85c4-a058a12f9623
-- title:
--   Theorem 4.16 -- lovasz_convex_iff_submodular
-- statement:
--   **Theorem 4.16** (Lovász, p.111). A set function $\rho : 2^V \to \mathbb R \cup \{+\infty\}$ with $\rho(\emptyset)=0$ and $\rho(V) < +\infty$ is submodular if and only if its Lovász extension $\hat\rho$ (Eq. (4.6)) is convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111, Theorem 4.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111, Theorem 4.16

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsConvexWithTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.111, Theorem 4.16, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.16 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.111). See the item's
`natural_language_statement` for the full statement. -/
theorem lovasz_convex_iff_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ0 : ρ ∅ = 0) (hρV : ρ Finset.univ ≠ ⊤) :
    (∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)) ↔ IsConvexWithTop (LovaszExtension ρ) := by sorry

end DiscreteConvex.MConvexSetsB
