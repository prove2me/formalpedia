-- Prove2me | Theorems.Thm_CGWH_isQuotientMap_snd_pullback
-- name    : CGWH.isQuotientMap_snd_pullback
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:19.744061+00:00
-- url     : https://prove2.me/theorems/05393100-1765-43f8-848c-5030fa1412c7
-- title:
--   In $\mathbf{CGWH}$, the pullback of a quotient map along any continuous map is a quotient map
-- statement:
--   Quotient maps of compactly generated weakly Hausdorff spaces are stable under arbitrary base change.
--
--   Conventions. A *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the *$k$-ification* $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). A topological space $X$ is *weakly Hausdorff* if the image $g(K)$ of every test map $g:K\to X$ is closed in $X$. For spaces $X,Y$ we write $X\times_0Y$ for the cartesian product with the product topology and $X\times Y:=k(X\times_0Y)$, which is the product in the category $\mathbf{CG}$ of compactly generated spaces when $X$ and $Y$ are compactly generated. A *quotient map* is a surjective map $f:X\to Y$ such that $V\subseteq Y$ is open if and only if $f^{-1}(V)$ is open in $X$.
--
--   Let $X,Y,T$ be compactly generated weakly Hausdorff spaces, let $f:X\to Y$ be a quotient map and let $g:T\to Y$ be a continuous map. The fibre product of $f$ and $g$ in the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces (equivalently, in $\mathbf{CG}$) is
--   $$X\times_{f,Y,g}T:=k\big(\{(x,t)\in X\times_0T\;:\;f(x)=g(t)\}\big),$$
--   the $k$-ification of the subspace $\{f(x)=g(t)\}$ of the product space $X\times_0T$.
--
--   **Statement.** The projection
--   $$f_T:X\times_{f,Y,g}T\longrightarrow T,\qquad (x,t)\longmapsto t,$$
--   is a quotient map.
--
--   This fails in the category of all topological spaces and in $\mathbf{CG}$: the paper's Example E.1.2.16 (adapted from Borceux) is a quotient map of finite, hence compactly generated, spaces with a base change that is not a quotient map. It is the key advantage of $\mathbf{CGWH}$: quotient maps are exactly its regular epimorphisms, so the statement says that regular epimorphisms are stable under pullback; this is the reason why $\mathbf{CGWH}$ is a regular category and why quotient maps are its universally effective epimorphisms (parts (7) and (14) of the source's Proposition E.2.3.15). The paper uses this stability systematically to describe the canonical topology on $\mathbf{CGWH}$ in its theory of topological stacks.
--
--   **Formalization Note.** All spaces live in one universe `u`; `CompactlyGeneratedSpace` is Mathlib's notion (the topology is coinduced by all continuous maps from compact Hausdorff spaces of `Type u`, no separation axiom) and `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff` (closed images of all continuous maps from compact Hausdorff spaces of `Type u`). The fibre product is the subtype `{p : X × T // f p.1 = g p.2}` of the product, endowed with `TopologicalSpace.compactlyGenerated` of its subspace topology (the $k$-ification); the map is `p ↦ p.1.2` and the target `T` carries its given topology. The hypotheses are those of the source (all three spaces compactly generated and weakly Hausdorff).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 856-857, Lemma E.2.3.6(6); classical reference (as cited by the paper for the proof of this lemma): N. Strickland, The category of CGWH spaces (available online), Prop. 2.32

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isQuotientMap_snd_pullback
    {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    [CompactlyGeneratedSpace T] [WeaklyHausdorffSpace T]
    {f : X → Y} (hf : IsQuotientMap f) {g : T → Y} (hg : Continuous g) :
    @IsQuotientMap {p : X × T // f p.1 = g p.2} T
      (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _
      (fun p => p.1.2) := by sorry

end CGWH
