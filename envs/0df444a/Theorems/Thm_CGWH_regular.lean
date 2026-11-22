-- Prove2me | Theorems.Thm_CGWH_regular
-- name    : CGWH.regular
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:48.341423+00:00
-- url     : https://prove2.me/theorems/09d579b3-cfc1-4f48-a3fc-dfaf34b1473a
-- title:
--   The category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces is a regular category
-- statement:
--   The category of compactly generated weakly Hausdorff spaces is regular.
--
--   Conventions. A topological space is *compactly generated* if a subset is closed as soon as its preimage under every continuous map from a compact Hausdorff space is closed (no separation axiom), and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed. $\mathbf{CGWH}$ is the category of compactly generated weakly Hausdorff spaces and continuous maps. A category $\mathcal C$ is *regular* (in the sense of Mathlib's `CategoryTheory.Regular`; the source refers to Borceux's Handbook and to van Oosten's notes for the notion, and the definitions of the literature agree for categories with finite limits and coequalizers, such as $\mathbf{CGWH}$) if
--
--   1. $\mathcal C$ has all finite limits,
--   2. every kernel pair $X\times_YX\rightrightarrows X$ in $\mathcal C$ has a coequalizer,
--   3. regular epimorphisms are stable under base change: in every pullback square
--   $$\begin{array}{ccc}P&\xrightarrow{\ f'\ }&T\\ \downarrow&&\downarrow\\ X&\xrightarrow{\ f\ }&Y\end{array}$$
--   in which $f$ is a regular epimorphism (a coequalizer of some pair of morphisms), $f'$ is a regular epimorphism.
--
--   **Statement.** The category $\mathbf{CGWH}$ is a regular category.
--
--   Since the regular epimorphisms of $\mathbf{CGWH}$ are exactly the quotient maps, condition 3 says that quotient maps of compactly generated weakly Hausdorff spaces are stable under base change, which fails for general topological spaces and for compactly generated spaces. Regularity has the usual structural consequences (the source refers to Borceux, Ch. 2, Thm. 2.1.3): every morphism of $\mathbf{CGWH}$ factors as a regular epimorphism followed by a monomorphism, i.e. every continuous map of compactly generated weakly Hausdorff spaces factors as a quotient map followed by a continuous injection, the factorization is unique up to a unique homeomorphism and it is preserved by base change (part (13) of the source's proposition). The paper does not use the general theory of regular categories, but uses the stability of quotient maps under base change systematically in its treatment of topological stacks.
--
--   **Formalization Note.** `CGWH.CGWHCat.{u}` (definition file `CGWH_WeakHausdorff`) is the full subcategory of Mathlib's category `CompactlyGenerated.{u, u}` on the weakly Hausdorff spaces. `CategoryTheory.Regular` is Mathlib's class of regular categories; it is a proposition, extending `HasFiniteLimits`, with the two further fields `hasCoequalizer_of_isKernelPair` (every kernel pair has a coequalizer) and `regularEpiIsStableUnderBaseChange` (the morphism property `MorphismProperty.regularEpi`, i.e. `IsRegularEpi`, is stable under base change). The source's Definition E.2.3.14 words regularity as condition 3 only, for categories with all small limits and colimits, and refers to Borceux for the definition.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 862 (proof on pp. 864-865), Proposition E.2.3.15 (13), (14), with Definition E.2.3.14; classical reference (as cited by the paper for the definition of a regular category): F. Borceux, Handbook of Categorical Algebra, 2. Categories and Structures, Cambridge University Press, 1994, Ch. 2, Def. 2.1.1; J. van Oosten, Basic Category Theory, BRICS LS-95-1, Aarhus (1995), Def. 4.1

import Definitions.Def_CGWH_WeakHausdorff

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem regular : Regular CGWHCat.{u} := by sorry

end CGWH
