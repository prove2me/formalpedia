-- Prove2me | Theorems.Thm_CGSpace_cartesianClosed
-- name    : CGSpace.cartesianClosed
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:23.7481+00:00
-- url     : https://prove2.me/theorems/addc758c-4bf2-4880-ac22-21383be28e5a
-- title:
--   The category $\mathbf{CG}$ of compactly generated spaces is cartesian closed
-- statement:
--   Cartesian closedness of the category of compactly generated spaces.
--
--   Let $\mathbf{CG}$ be the category of compactly generated topological spaces (spaces whose topology is coinduced by all continuous maps from compact Hausdorff spaces; no separation axiom) and continuous maps. It has finite products: the terminal object is the one-point space, and the product of $X$ and $Y$ in $\mathbf{CG}$ is $X\times Y=k(X\times_0Y)$, the $k$-ification of the product topology.
--
--   **Statement.** The category $\mathbf{CG}$ is cartesian closed: it has finite products (in particular a terminal object and binary products), and for every object $Y$ the product functor
--   $$Y\times(-):\mathbf{CG}\longrightarrow\mathbf{CG}$$
--   has a right adjoint.
--
--   In the source (Proposition E.1.2.13) the right adjoint is the function space functor $Z\mapsto\mathscr{C}ont_k(Y,Z)=k(\mathrm{C}(Y,Z))$, where $\mathrm{C}(Y,Z)$ carries the compact-open topology defined by test maps from compact Hausdorff spaces; the adjunction bijection is currying and the counit is the evaluation map. Cartesian closedness is one of the defining properties of a convenient category of spaces: product functors commute with all colimits, which is what the paper uses to prove that products of quotient maps of compactly generated spaces are quotient maps.
--
--   **Formalization Note.** `CompactlyGenerated.{u, u}` is Mathlib's category of compactly generated spaces in `Type u` with test spaces in `CompHaus.{u}`; both universe parameters are equal because the function space of two spaces of `Type u` lives in `Type u`. Mathlib provides no instance of finite products for this category, so their existence is part of the statement (`Limits.HasFiniteProducts` is a proposition, and the product functor is determined up to isomorphism). In Mathlib's framework of $X$-generated spaces (`Mathlib.Topology.Convenient.HomSpace`) the underlying bijection of Hom-sets is `Topology.ContinuousMapGeneratedBy.curryEquiv`; the cartesian closed structure is a TODO there (`Mathlib.Topology.Convenient.GeneratedBy`, `Mathlib.Topology.Convenient.Category`), as it is for the category `CompactlyGenerated` itself (`Mathlib.Topology.Category.CompactlyGenerated`). `Limits.prod.functor.obj Y` is the functor $Z\mapsto Y\times Z$ and `Functor.IsLeftAdjoint` asserts the existence of a right adjoint. The abstract statement does not identify the right adjoint; its identification with $\mathscr{C}ont_k$ is the content of the exponential law `CGSpace.exponential_law`. The enrichment of $\mathbf{CG}$ over itself asserted in the source is not part of the Lean statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 841, Proposition E.1.2.13; classical reference (as cited by the paper at this place): N. Strickland, The category of CGWH spaces (available online), Prop. 2.12 (resting on Prop. 2.11); see also M. Escardó, J. Lawson, A. Simpson, Comparing Cartesian closed categories of (core) compactly generated spaces, Topology and its Applications 143 (2004), 105-145, §5 (cited on p. 835)

import Mathlib

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem cartesianClosed :
    ∃ _ : Limits.HasFiniteProducts CompactlyGenerated.{u, u},
      ∀ Y : CompactlyGenerated.{u, u}, (Limits.prod.functor.obj Y).IsLeftAdjoint := by sorry

end CGSpace
