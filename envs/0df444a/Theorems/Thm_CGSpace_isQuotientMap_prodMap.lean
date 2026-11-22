-- Prove2me | Theorems.Thm_CGSpace_isQuotientMap_prodMap
-- name    : CGSpace.isQuotientMap_prodMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:22.798204+00:00
-- url     : https://prove2.me/theorems/7312c753-5bf6-4140-b769-8c7b836733da
-- title:
--   The product of two quotient maps of compactly generated spaces is a quotient map for the $k$-ified product topologies
-- statement:
--   Stability of quotient maps under products in the category of compactly generated spaces.
--
--   Let $X,Y,X',Y'$ be compactly generated topological spaces (a subset is open as soon as its preimage under every continuous map from a compact Hausdorff space is open; no separation axiom). A map is a *quotient map* (*submersive* in the source) if it is surjective and a subset of the target is open if and only if its preimage is open. Let $X\times Y:=k(X\times_0Y)$ and $X'\times Y':=k(X'\times_0Y')$ be the products in the category $\mathbf{CG}$ of compactly generated spaces, i.e. the $k$-ifications of the product topologies.
--
--   **Statement.** If $f:X\to X'$ and $g:Y\to Y'$ are quotient maps, then
--   $$f\times g:X\times Y\longrightarrow X'\times Y',\qquad (x,y)\longmapsto(f(x),g(y)),$$
--   is a quotient map.
--
--   The statement fails for the product topologies $X\times_0Y\to X'\times_0Y'$: for the quotient map $f:\mathbf{Q}\to\mathbf{Q}/\mathbf{Z}$ collapsing the integers to a point, $f\times\mathrm{id}_{\mathbf{Q}}$ is not a quotient map (Example E.1.2.18 of the paper). This is one of the main reasons for working with compactly generated spaces; in the paper the lemma is deduced from the cartesian closedness of $\mathbf{CG}$ (product functors preserve coequalizers) and it is the source of the good behaviour of quotient (submersive) maps in the sites of Appendix E.
--
--   **Formalization Note.** `CompactlyGeneratedSpace X` is Mathlib's notion for `X : Type u`: the topology of $X$ is coinduced by all continuous maps from compact Hausdorff spaces in the same universe (`CompHaus.{u}`), with no separation axiom on $X$. The two $k$-ified product topologies are written explicitly as `TopologicalSpace.compactlyGenerated (X × Y)` and `TopologicalSpace.compactlyGenerated (X' × Y')` in the arguments of `@IsQuotientMap`, because the default instance on a product type is the product topology, for which the statement is false. `Topology.IsQuotientMap` includes surjectivity.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 842, Lemma E.1.2.17; classical reference (as cited by the paper in Remark E.1.2.15): L. G. Lewis, Jr., The stable category and generalized Thom spectra, Ph.D. thesis, University of Chicago, 1978, §5, Prop. 5.8

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem isQuotientMap_prodMap
    {X X' Y Y' : Type u} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
    [TopologicalSpace Y'] [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    [CompactlyGeneratedSpace X'] [CompactlyGeneratedSpace Y']
    {f : X → X'} {g : Y → Y'} (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    @IsQuotientMap (X × Y) (X' × Y') (TopologicalSpace.compactlyGenerated.{u} (X × Y))
      (TopologicalSpace.compactlyGenerated.{u} (X' × Y')) (Prod.map f g) := by sorry

end CGSpace
