-- Prove2me | Theorems.Thm_CGSpace_isRegularEpi_effectiveEpi_isQuotientMap_tfae
-- name    : CGSpace.isRegularEpi_effectiveEpi_isQuotientMap_tfae
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:23.191175+00:00
-- url     : https://prove2.me/theorems/3dca1687-235d-46a8-a5b5-012020150074
-- title:
--   In the category $\mathbf{CG}$ of compactly generated spaces: regular epimorphisms = effective epimorphisms = quotient maps
-- statement:
--   Characterization of the quotient maps between compactly generated spaces as the regular, equivalently effective, epimorphisms of the category $\mathbf{CG}$.
--
--   Let $\mathbf{CG}$ be the category of compactly generated topological spaces (the topology is coinduced by all continuous maps from compact Hausdorff spaces; no separation axiom) and continuous maps. A continuous map $f:X\to Y$ is a *quotient map* (*submersive map* in the terminology of the source) if it is surjective and a subset $V\subseteq Y$ is open if and only if $f^{-1}(V)$ is open in $X$.
--
--   **Statement.** For a continuous map $f:X\to Y$ between compactly generated spaces the following are equivalent:
--
--   1. $f$ is a regular epimorphism in $\mathbf{CG}$: there are a compactly generated space $R$ and continuous maps $s,t:R\rightrightarrows X$ such that $f$ is a coequalizer of $s$ and $t$ in $\mathbf{CG}$ (i.e. there is a homeomorphism $c:\mathrm{coeq}(s,t)\to Y$ with $c\circ p=f$ for the canonical map $p:X\to\mathrm{coeq}(s,t)$);
--   2. $f$ is an effective epimorphism in $\mathbf{CG}$: it is the coequalizer in $\mathbf{CG}$ of its kernel pair $p_1,p_2:X\times_{f,Y,f}X\rightrightarrows X$, the two projections of the fibre product formed in $\mathbf{CG}$;
--   3. $f$ is a quotient map.
--
--   Although quotient maps are thus the regular epimorphisms, $\mathbf{CG}$ is not a regular category, because quotient maps of compactly generated spaces are not stable under base change (Example E.1.2.16 of the paper). The paper combines the characterization with the cartesian closedness of $\mathbf{CG}$ to show that products of quotient maps are quotient maps.
--
--   **Formalization Note.** `CompactlyGenerated.{u, w}` is Mathlib's category of `u`-compactly generated spaces in `Type w`. `IsRegularEpi f` is the proposition that `f` is a coequalizer of some parallel pair. Mathlib's `EffectiveEpi f` is defined without reference to pullbacks: every morphism $e:X\to W$ of $\mathbf{CG}$ satisfying $e\circ g_1=e\circ g_2$ for all pairs of morphisms $g_1,g_2:T\to X$ with $f\circ g_1=f\circ g_2$ factors uniquely through $f$; since $\mathbf{CG}$ has fibre products this is equivalent to condition 2. `ConcreteCategory.hom f` is the underlying continuous map of the morphism `f`, and `Topology.IsQuotientMap` includes surjectivity. Mathlib has the analogous statement only for the category `TopCat` (`TopCat.effectiveEpi_iff_isQuotientMap`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 841, Lemma E.1.2.14 and Remark E.1.2.15; classical reference (as cited by the paper): L. G. Lewis, Jr., The stable category and generalized Thom spectra, Ph.D. thesis, University of Chicago, 1978, §5, Lemma 5.7

import Mathlib

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u w

namespace CGSpace

theorem isRegularEpi_effectiveEpi_isQuotientMap_tfae
    {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    [IsRegularEpi f, EffectiveEpi f, IsQuotientMap (ConcreteCategory.hom f)].TFAE := by sorry

end CGSpace
