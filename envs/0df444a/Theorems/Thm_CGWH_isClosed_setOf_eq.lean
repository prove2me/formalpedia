-- Prove2me | Theorems.Thm_CGWH_isClosed_setOf_eq
-- name    : CGWH.isClosed_setOf_eq
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:43.166966+00:00
-- url     : https://prove2.me/theorems/000151f4-8417-41b0-903c-c0fec919ab2e
-- title:
--   The coincidence set of two continuous maps from a compactly generated space to a weakly Hausdorff space is closed
-- statement:
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$.
--
--   The weak Hausdorff analogue of the fact that two continuous maps into a Hausdorff space agree on a closed set.
--
--   **Statement.** Let $X$ be a compactly generated topological space, let $Y$ be a weakly Hausdorff topological space and let $f,g:X\to Y$ be continuous maps. Then the coincidence set (the equalizer of $f$ and $g$)
--   $$\operatorname{eq}(f,g)=\{x\in X\;:\;f(x)=g(x)\}=(f,g)^{-1}(\Delta_Y)$$
--   is closed in $X$.
--
--   Here $\Delta_Y\subseteq Y\times Y$ is the diagonal; it need not be closed for the product topology (a weakly Hausdorff space need not be Hausdorff), but it is $k$-closed, and $k$-closed subsets of a compactly generated space are closed. This is the mechanism behind most separation arguments in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces: the paper uses it to show that a continuous map with dense image is an epimorphism of $\mathbf{CGWH}$ (proof of Proposition E.2.3.15(2)), that regular monomorphisms are closed embeddings (proof of Proposition E.2.3.15(3)), that continuous sections are closed embeddings (Lemma E.2.3.4) and that kernel pairs of maps into weakly Hausdorff spaces are closed (proofs of Lemma E.2.2.4 and Lemma E.2.3.8).
--
--   **Formalization Note.** `X Y : Type u`; `CompactlyGeneratedSpace X` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`) and `CGWH.WeaklyHausdorffSpace Y` is the class of the definition file `CGWH_WeakHausdorff`. In the source the statement occurs inside proofs, for compactly generated weakly Hausdorff spaces $X$ and $Y$; only the hypotheses that the argument uses are kept ($X$ compactly generated, $Y$ weakly Hausdorff). The conclusion has the shape of Mathlib's `isClosed_eq` (which assumes $Y$ Hausdorff).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 855-856 and 864, proof of Lemma E.2.3.4 and proof of Proposition E.2.3.15(2)-(3) (see also the proof of Lemma E.2.2.4, p. 852)

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isClosed_setOf_eq
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace Y] {f g : X → Y}
    (hf : Continuous f) (hg : Continuous g) : IsClosed {x : X | f x = g x} := by sorry

end CGWH
