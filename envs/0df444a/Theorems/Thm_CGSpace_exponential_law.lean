-- Prove2me | Theorems.Thm_CGSpace_exponential_law
-- name    : CGSpace.exponential_law
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:37.603868+00:00
-- url     : https://prove2.me/theorems/64e55b57-6888-46c9-9b70-133664953887
-- title:
--   Exponential law for compactly generated spaces: $\mathscr{C}ont_k(X\times Y,Z)\cong\mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z))$
-- statement:
--   The exponential law (currying homeomorphism) for function spaces of compactly generated spaces.
--
--   Let $X,Y,Z$ be compactly generated topological spaces: a subset is open as soon as its preimage under every continuous map from a compact Hausdorff space is open (no separation axiom). Write $X\times Y:=k(X\times_0 Y)$ for the product in the category $\mathbf{CG}$ of compactly generated spaces, i.e. the $k$-ification of the product topology. For compactly generated spaces $A,B$ let
--   $$\mathscr{C}ont_k(A,B):=k\big(\mathrm{C}(A,B)\big)$$
--   be the compactly generated function space: the set of continuous maps $A\to B$ with the $k$-ification of the compact-open topology having as sub-base the sets $N(g,K,U)=\{f:(f\circ g)(K)\subseteq U\}$, where $K$ is a compact Hausdorff space, $g:K\to A$ is continuous and $U\subseteq B$ is open.
--
--   **Statement.** For every continuous map $f:X\times Y\to Z$ and every $x\in X$ the map $f(x,\cdot):Y\to Z$ is continuous, the map $x\mapsto f(x,\cdot)$ is continuous from $X$ to $\mathscr{C}ont_k(Y,Z)$, and the resulting map
--   $$\theta_{X,Y,Z}:\mathscr{C}ont_k(X\times Y,Z)\longrightarrow\mathscr{C}ont_k\big(X,\mathscr{C}ont_k(Y,Z)\big),\qquad \theta_{X,Y,Z}(f)(x)(y)=f(x,y),$$
--   is a homeomorphism.
--
--   In particular $\theta_{X,Y,Z}$ is a bijection: a map $X\to\mathscr{C}ont_k(Y,Z)$ is continuous if and only if the corresponding map $X\times Y\to Z$ is continuous on the $k$-product. This is the adjunction $(-)\times Y\dashv\mathscr{C}ont_k(Y,-)$ that makes $\mathbf{CG}$ cartesian closed with internal hom $\mathscr{C}ont_k$; the paper derives from it that products of quotient maps in $\mathbf{CG}$ are quotient maps and that push-forward along (closed) embeddings is a (closed) embedding of function spaces.
--
--   **Formalization Note.** The statement uses the definition file `CGSpace_FunctionSpace`: `CGSpace.KSpace (X × Y)` is $k(X\times_0Y)$ and `CGSpace.ContK A B` is $\mathscr{C}ont_k(A,B)$; `ContK.toContinuousMap` and `KSpace.mk` are the identity bijections of these type synonyms. The Lean statement asserts the existence of a homeomorphism `e` satisfying $e(f)(x)(y)=f(x,y)$ for all $f,x,y$; this formula determines `e` and encodes at once that currying is well defined (its values are continuous maps into $\mathscr{C}ont_k(Y,Z)$), bijective and bicontinuous. All spaces live in one universe `u` and `CompactlyGeneratedSpace X` is Mathlib's notion for `X : Type u`: the topology of $X$ is coinduced by all continuous maps from compact Hausdorff spaces in the same universe (`CompHaus.{u}`), with no separation axiom on $X$. The hypothesis that $Z$ is compactly generated is kept as in the source.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 837-840, Lemma E.1.2.12; classical reference (as cited by the paper on p. 837): L. G. Lewis, Jr., The stable category and generalized Thom spectra, Ph.D. thesis, University of Chicago, 1978, Thm. 5.5; N. Strickland, The category of CGWH spaces (available online), Prop. 2.20; C. Rezk, Compactly generated spaces (available online), Prop. 8.8

import Definitions.Def_CGSpace_FunctionSpace

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem exponential_law
    (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] [CompactlyGeneratedSpace Z] :
    ∃ e : ContK (KSpace (X × Y)) Z ≃ₜ ContK X (ContK Y Z),
      ∀ (f : ContK (KSpace (X × Y)) Z) (x : X) (y : Y),
        ContK.toContinuousMap (ContK.toContinuousMap (e f) x) y =
          ContK.toContinuousMap f (KSpace.mk (x, y)) := by sorry

end CGSpace
