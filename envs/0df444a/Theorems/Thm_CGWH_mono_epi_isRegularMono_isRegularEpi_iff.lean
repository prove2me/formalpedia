-- Prove2me | Theorems.Thm_CGWH_mono_epi_isRegularMono_isRegularEpi_iff
-- name    : CGWH.mono_epi_isRegularMono_isRegularEpi_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:29.012113+00:00
-- url     : https://prove2.me/theorems/2493bf61-0b08-44a1-a494-60b207703858
-- title:
--   Monomorphisms, epimorphisms, regular monomorphisms and regular epimorphisms of the category $\mathbf{CGWH}$
-- statement:
--   Concrete description of the monomorphisms, epimorphisms, regular monomorphisms and regular epimorphisms in the category of compactly generated weakly Hausdorff spaces.
--
--   Let $\mathbf{CGWH}$ be the category whose objects are the compactly generated weakly Hausdorff topological spaces (the topology is determined by the continuous maps from compact Hausdorff spaces, and the image of every such map is closed) and whose morphisms are the continuous maps. In a category, a monomorphism is *regular* if it is the equalizer of some pair of parallel morphisms, and an epimorphism is *regular* if it is the coequalizer of some pair of parallel morphisms.
--
--   **Statement.** Let $f:X\to Y$ be a morphism of $\mathbf{CGWH}$, i.e. a continuous map between compactly generated weakly Hausdorff spaces. Then:
--
--   1. $f$ is a monomorphism of $\mathbf{CGWH}$ if and only if $f$ is injective;
--   2. $f$ is an epimorphism of $\mathbf{CGWH}$ if and only if $f$ has dense image, i.e. $\overline{f(X)}=Y$;
--   3. $f$ is a regular monomorphism of $\mathbf{CGWH}$ if and only if $f$ is a closed embedding (a homeomorphism onto a closed subspace of $Y$);
--   4. $f$ is a regular epimorphism of $\mathbf{CGWH}$ if and only if $f$ is a quotient map (surjective, and $V\subseteq Y$ is open iff $f^{-1}(V)$ is open).
--
--   In contrast with the category of all topological spaces, epimorphisms of $\mathbf{CGWH}$ need not be surjective and regular monomorphisms are closed embeddings rather than arbitrary embeddings, exactly as for Hausdorff spaces; the weak Hausdorff condition enters through the closedness of equalizers (the diagonal is closed in the product of $\mathbf{CG}$) and through the fact that the quotient of $Y$ by a closed subspace stays in $\mathbf{CGWH}$. Part 4, together with the stability of quotient maps under base change, is the reason why $\mathbf{CGWH}$ is a regular category (part (14) of the source's proposition); the paper uses these identifications to describe the canonical topology on $\mathbf{CGWH}$.
--
--   **Formalization Note.** `CGWH.CGWHCat.{u}` is the category of the definition file `CGWH_WeakHausdorff`; for a morphism `f : X ⟶ Y` the underlying continuous map is `ConcreteCategory.hom f.hom : C(X.obj, Y.obj)`, and injectivity, `DenseRange`, `IsClosedEmbedding` and `IsQuotientMap` are stated for its underlying function. `IsRegularMono` and `IsRegularEpi` are Mathlib's propositional classes ("there exists a presentation of `f` as an equalizer, resp. coequalizer, of a pair of morphisms"). The statement is the conjunction of parts (1)-(4) of the source's Proposition E.2.3.15; its parts (5)-(14) are not included.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 862 (proof on p. 864), Proposition E.2.3.15, parts (1)-(4), with Definition E.2.3.14

import Definitions.Def_CGWH_WeakHausdorff

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem mono_epi_isRegularMono_isRegularEpi_iff {X Y : CGWHCat.{u}} (f : X ⟶ Y) :
    (Mono f ↔ Function.Injective (ConcreteCategory.hom f.hom)) ∧
    (Epi f ↔ DenseRange (ConcreteCategory.hom f.hom)) ∧
    (IsRegularMono f ↔ IsClosedEmbedding (ConcreteCategory.hom f.hom)) ∧
    (IsRegularEpi f ↔ IsQuotientMap (ConcreteCategory.hom f.hom)) := by sorry

end CGWH
