-- Prove2me | Theorems.Thm_CGWH_isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae
-- name    : CGWH.isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:46.57037+00:00
-- url     : https://prove2.me/theorems/90621dec-dd51-4c55-9212-915c2e9c54da
-- title:
--   In $\mathbf{CGWH}$: quotient maps $=$ effective epimorphisms $=$ universally effective epimorphisms
-- statement:
--   Characterization of the effective and of the universally effective epimorphisms of the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces.
--
--   Conventions. A topological space is *compactly generated* if a subset is closed as soon as its preimage under every continuous map from a compact Hausdorff space is closed (no separation axiom), and *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space is closed. $\mathbf{CGWH}$ is the category of compactly generated weakly Hausdorff spaces and continuous maps; it has all small limits and colimits. A *quotient map* (called a submersive map in the source) is a surjective map $f:X\to Y$ such that $V\subseteq Y$ is open if and only if $f^{-1}(V)$ is open in $X$.
--
--   In a category with kernel pairs, a morphism $f:X\to Y$ is an *effective epimorphism* if it is the coequalizer of its kernel pair $X\times_YX\rightrightarrows X$; equivalently, every morphism $e:X\to W$ such that $e\circ a=e\circ b$ whenever $f\circ a=f\circ b$ factors uniquely through $f$. It is a *universally effective epimorphism* if every base change of $f$ is an effective epimorphism: for every pullback square
--   $$\begin{array}{ccc}P&\xrightarrow{\ f'\ }&T\\ \downarrow&&\downarrow{\scriptstyle g}\\ X&\xrightarrow{\ f\ }&Y\end{array}$$
--   the morphism $f':P\to T$ is an effective epimorphism.
--
--   **Statement.** For a morphism $f:X\to Y$ of $\mathbf{CGWH}$ the following are equivalent:
--
--   1. the underlying continuous map of $f$ is a quotient map;
--   2. $f$ is an effective epimorphism of $\mathbf{CGWH}$;
--   3. $f$ is a universally effective epimorphism of $\mathbf{CGWH}$.
--
--   Together with the platform statement `CGWH.mono_epi_isRegularMono_isRegularEpi_iff` (regular epimorphisms are the quotient maps) this covers Lemma E.2.3.8 and parts (4), (6) and (7) of Proposition E.2.3.15 of the source. The equivalence with 3 fails in the category of all topological spaces and in the category of compactly generated spaces, where a base change of a quotient map need not be a quotient map; in $\mathbf{CGWH}$ it holds because quotient maps are stable under base change (Lemma E.2.3.6(6), platform statement `CGWH.isQuotientMap_snd_pullback`). It is the reason for the paper's choice of $\mathbf{CGWH}$: quotient maps give a concrete description of the canonical Grothendieck topology on $\mathbf{CGWH}$, on which the paper builds its theory of topological stacks.
--
--   **Formalization Note.** `CGWH.CGWHCat.{u}` (definition file `CGWH_WeakHausdorff`) is the full subcategory of Mathlib's category `CompactlyGenerated.{u, u}` on the weakly Hausdorff spaces; `ConcreteCategory.hom f.hom` is the continuous map underlying `f`. `EffectiveEpi` is Mathlib's notion (existence of an `EffectiveEpiStruct`: the factorization property above, which does not require kernel pairs to exist and agrees with "coequalizer of its kernel pair" when they do). Condition 3 is stated with pullback squares instead of chosen pullbacks, because the existence of pullbacks in `CGWHCat` is a theorem and not an instance: for all objects `P`, `T` and morphisms `fst : P ⟶ X`, `snd : P ⟶ T`, `g : T ⟶ Y` with `IsPullback fst snd f g` (i.e. `fst ≫ f = snd ≫ g` is a pullback square), `snd` is an effective epimorphism. The statement is a `List.TFAE`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 858-859 and 862 (proof on p. 864), Lemma E.2.3.8 and Proposition E.2.3.15 (6), (7), with Definition E.2.3.14

import Definitions.Def_CGWH_WeakHausdorff

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae {X Y : CGWHCat.{u}} (f : X ⟶ Y) :
    [IsQuotientMap (ConcreteCategory.hom f.hom),
      EffectiveEpi f,
      ∀ ⦃P T : CGWHCat.{u}⦄ (fst : P ⟶ X) (snd : P ⟶ T) (g : T ⟶ Y),
        IsPullback fst snd f g → EffectiveEpi snd].TFAE := by sorry

end CGWH
