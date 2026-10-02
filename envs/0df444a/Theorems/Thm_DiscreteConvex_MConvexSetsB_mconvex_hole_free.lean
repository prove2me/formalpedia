-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_hole_free
-- name    : DiscreteConvex.MConvexSetsB.mconvex_hole_free
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:09.93786+00:00
-- url     : https://prove2.me/theorems/126d0316-a9e9-478b-bd5c-a34682ba3769
-- title:
--   Theorem 4.12 -- mconvex_hole_free
-- statement:
--   **Theorem 4.12** (p.108), the hole-free property. For an M-convex set $B \subseteq \mathbb Z^V$, $B = \overline B \cap \mathbb Z^V$, where $\overline B$ is the convex hull of $B$: an M-convex set contains exactly the integer points of its own convex hull, with no interior integer points missing ("holes").
--
--   **Formalization Note.** The book's statement is printed as "$B = B \cap \mathbb Z^V$", with the overline diacritic on the second occurrence lost by text extraction; the mathematical content (confirmed against the surrounding paragraph, which introduces this result as what lets one identify an M-convex set with its convex hull) is $B = \overline B \cap \mathbb Z^V$, formalized here via `IntEmbed` (the real embedding of $B$) and `convexHull`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108, Theorem 4.12.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108, Theorem 4.12

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.108, Theorem 4.12, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.12 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.108). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_hole_free {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    IntEmbed B = convexHull ℝ (IntEmbed B) ∩ IntPts := by sorry

end DiscreteConvex.MConvexSetsB
