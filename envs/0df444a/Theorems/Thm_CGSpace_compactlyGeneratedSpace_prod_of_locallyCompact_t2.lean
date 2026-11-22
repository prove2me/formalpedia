-- Prove2me | Theorems.Thm_CGSpace_compactlyGeneratedSpace_prod_of_locallyCompact_t2
-- name    : CGSpace.compactlyGeneratedSpace_prod_of_locallyCompact_t2
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:27.969966+00:00
-- url     : https://prove2.me/theorems/cc8f9b4e-d31c-4dcd-b207-37522e021b9d
-- title:
--   The product of a compactly generated space and a locally compact Hausdorff space is compactly generated
-- statement:
--   Compact generation of the topological product of a compactly generated space with a locally compact Hausdorff space.
--
--   Let $X$ be a compactly generated topological space: a subset of $X$ is open as soon as its preimage under every continuous map from a compact Hausdorff space is open (no separation axiom on $X$). Let $Y$ be a locally compact Hausdorff space, and let $X\times_0Y$ denote the cartesian product with the product topology.
--
--   **Statement.** The space $X\times_0Y$ is compactly generated.
--
--   Consequently $k(X\times_0Y)=X\times_0Y$, i.e. the topological product computes the product of $X$ and $Y$ in the category $\mathbf{CG}$ of compactly generated spaces. In general the product topology of two compactly generated spaces is not compactly generated (for instance $(\mathbf{Q}/\mathbf{Z})\times_0\mathbf{Q}$ is not); see Remark E.1.2.20 of the paper for the role of the Hausdorff hypothesis on $Y$. The result identifies $k$-products with ordinary products in the most frequently used cases, for instance for $Y=[0,1]$ (homotopies) and for $Y$ a compact Hausdorff test space.
--
--   **Formalization Note.** `CompactlyGeneratedSpace X` is Mathlib's notion for `X : Type u`: the topology of $X$ is coinduced by all continuous maps from compact Hausdorff spaces in the same universe (`CompHaus.{u}`), with no separation axiom on $X$. `LocallyCompactSpace Y` means that every point of $Y$ has a neighbourhood basis of compact sets; together with `T2Space Y` this is the usual notion of a locally compact Hausdorff space. `X × Y` carries the product topology. The companion statement that a locally compact Hausdorff space is itself compactly generated (part (1) of the proposition) is an instance in Mathlib.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 843, Proposition E.1.2.19(2); classical reference (as cited by the paper): N. Strickland, The category of CGWH spaces (available online), Prop. 2.6

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem compactlyGeneratedSpace_prod_of_locallyCompact_t2
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [LocallyCompactSpace Y] [T2Space Y] :
    CompactlyGeneratedSpace (X × Y) := by sorry

end CGSpace
