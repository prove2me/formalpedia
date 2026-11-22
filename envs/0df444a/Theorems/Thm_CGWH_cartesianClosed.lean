-- Prove2me | Theorems.Thm_CGWH_cartesianClosed
-- name    : CGWH.cartesianClosed
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:21.868802+00:00
-- url     : https://prove2.me/theorems/aa73aa26-5337-41cf-9e0b-af6bde48c806
-- title:
--   The category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces is cartesian closed
-- statement:
--   The category of compactly generated weakly Hausdorff spaces is cartesian closed.
--
--   Let $\mathbf{CGWH}$ be the category whose objects are the compactly generated weakly Hausdorff topological spaces and whose morphisms are the continuous maps. Here a space is *compactly generated* if its topology is determined by the continuous maps into it from compact Hausdorff spaces, and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed.
--
--   **Statement.** The category $\mathbf{CGWH}$ has finite products, and for every object $Y$ the functor
--   $$Y\times(-):\mathbf{CGWH}\longrightarrow\mathbf{CGWH},\qquad X\longmapsto Y\times X,$$
--   has a right adjoint.
--
--   The product in $\mathbf{CGWH}$ is the product of the category $\mathbf{CG}$ of compactly generated spaces, $Y\times X=k(Y\times_0X)$ (the $k$-ification of the product topology), the terminal object is the one-point space, and the right adjoint of $Y\times(-)$ is $X\mapsto\mathscr{C}ont_k(Y,X)$, the set of continuous maps with the $k$-ified compact-open topology: $\mathbf{CGWH}$ inherits the cartesian closed structure of $\mathbf{CG}$ because the function space into a weakly Hausdorff space is weakly Hausdorff. Cartesian closedness fails for the category of all topological spaces and is one of the main reasons for working with compactly generated spaces; the paper records it (Section E.2.2) among the properties that $\mathbf{CGWH}$ retains from $\mathbf{CG}$.
--
--   **Formalization Note.** `CGWH.CGWHCat.{u}` is the category of the definition file `CGWH_WeakHausdorff` (the full subcategory of Mathlib's `CompactlyGenerated.{u, u}` on the weakly Hausdorff objects). The Lean statement asserts `Limits.HasFiniteProducts` and that each functor `Limits.prod.functor.obj Y` ($X\mapsto Y\times X$) is a left adjoint; it does not identify the right adjoint with $\mathscr{C}ont_k(Y,-)$. This is the same abstract form as the platform theorem `CGSpace.cartesianClosed` for $\mathbf{CG}$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 854, Proposition E.2.2.10 (second assertion); classical reference (as cited by the paper at this place): N. Strickland, The category of CGWH spaces (available online), Prop. 2.24

import Definitions.Def_CGWH_WeakHausdorff

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem cartesianClosed :
    ∃ _ : Limits.HasFiniteProducts CGWHCat.{u},
      ∀ Y : CGWHCat.{u}, (Limits.prod.functor.obj Y).IsLeftAdjoint := by sorry

end CGWH
