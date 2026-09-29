-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion
-- name    : AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/95126f7a-ada9-5d43-abc5-fd2eaaebf5e9
-- title:
--   Degree-d sections of a closed subscheme of Pⁿ_A come from polynomials for d gg 0
-- statement:
--   Let $A$ be a Noetherian commutative ring, $n$ a natural number, $Z$ a scheme, and let $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous components of $A[X_0,\dots,X_n]$ be a closed immersion. Write $\pi$ for the structure morphism `ProjSpace.π A n` to $\operatorname{Spec} A$, so that $\iota$ followed by $\pi$ is the composite structure morphism of $Z$. The assertion is that there is a bound $d_2 \in \mathbb{N}$ such that for every $d \ge d_2$ the following holds. An element $x$ of `ProjSpace.twistFam` is a family assigning to each integer $e$ and each index $i \in \{0,\dots,n\}$ a section of $\mathcal{O}_Z$ over $\top \sqcap \iota^{-1}(D(X_i))$, where $\iota^{-1}(D(X_i))$ is `ProjSpace.pullbackChart ι i`, the preimage under $\iota$ of the basic open set of $\operatorname{Proj}$ attached to $X_i$. Suppose $x$ lies in the degree-$d$ piece of the graded module `ProjSpace.twistGradedModule`, i.e. $x$ vanishes in every degree $e \neq d$ and its degree-$d$ component satisfies the predicate `TwistCompat ι d ⊤`, the compatibility condition on the charts. Then there exist a polynomial $F \in A[X_0,\dots,X_n]$ and a proof that $F$ is homogeneous of degree $d$ such that, for every $i$, the section $x(d)(i)$ equals the restriction to $\top \sqcap \iota^{-1}(D(X_i))$ of the image under $\iota$ on sections over $D(X_i)$ of the section of $\mathcal{O}_{\operatorname{Proj}}$ determined (via `Proj.awayToSection`) by the homogeneous localisation element of degree $d$ with numerator $F$ and denominator $X_i^d$.
--
--   This is Serre's finiteness statement that for a closed subscheme $Z \subseteq \mathbb{P}^n_A$ over a Noetherian ring the map $A[X_0,\dots,X_n]_d \to \Gamma(Z,\mathcal{O}_Z(d))$ is surjective for all sufficiently large $d$, expressed entirely inside the graded module of twisted section families attached to $\iota$: every degree-$d$ element of that module is represented by a single homogeneous polynomial of degree $d$. It feeds the corresponding statement for degree-zero Čech cohomology classes of the twists, [`AlgebraicGeometry.ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] :
    ∃ d₂ : ℕ, ∀ d : ℕ, d₂ ≤ d →
      ∀ x : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι,
        x ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (d : ℤ) →
        ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          ∀ i : Fin (n + 1),
            x (d : ℤ) i =
              ProjSpace.restrictFun
                (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
                ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                  (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                    (HomogeneousLocalization.mk
                      { deg := d
                        num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                        den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                          (MvPolynomial.isHomogeneous_X_pow i d)⟩
                        den_mem := ⟨d, rfl⟩ }))) := by sorry
