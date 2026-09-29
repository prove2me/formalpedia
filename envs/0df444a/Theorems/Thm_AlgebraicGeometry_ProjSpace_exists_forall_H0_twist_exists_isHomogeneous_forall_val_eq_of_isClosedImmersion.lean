-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion
-- name    : AlgebraicGeometry.ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/6b857c9e-9a12-5650-8ef6-986f9eac48c2
-- title:
--   Large twists of a closed subscheme of Pⁿ_A: 0-cocycles come from forms
-- statement:
--   Let $A$ be a Noetherian commutative ring, $n$ a natural number, $Z$ a scheme, and let $\iota : Z \to \operatorname{Proj} A[x_0,\dots,x_n]$ be a closed immersion, where the graded algebra is $A[x_0,\dots,x_n] =$ `MvPolynomial (Fin (n+1)) A` with its homogeneous-component grading. Write $\pi$ for the composite of $\iota$ with the structure morphism `ProjSpace.π A n : Proj … ⟶ Spec A`, and let `stdCoverPullback ι` be the ordered affine cover of $Z$ by the opens $\iota^{-1}D_+(x_j)$, indexed by $j$ in a copy of $\mathrm{Fin}(n+1)$. The assertion is that there is $d_2 \in \mathbb N$ such that for every $d \ge d_2$ and every $0$-cocycle $c$ of the $\mathcal O$-module presheaf `ProjSpace.twist π ι d` for this cover — that is, every element of the kernel of the Čech differential on $0$-cochains, which assigns to each index $s$ (a strictly monotone map $\mathrm{Fin}\,1 \to$ the index set, so in effect to a single chart) a section of the $d$-th twist over the open `inter s` — there exist $F \in A[x_0,\dots,x_n]$ homogeneous of degree $d$ with the following property: for every such $s$ and every $j \in \mathrm{Fin}(n+1)$, the $j$-th component $(c\,s).\mathrm{val}\ j \in \Gamma(Z, \mathrm{inter}\,s \cap \iota^{-1}D_+(x_j))$ equals the restriction along `inf_le_right` of $\iota^{\sharp}$ applied to the section of $\mathcal O(d)$ on $D_+(x_j)$ attached, via `Proj.awayToSection`, to the homogeneous localization $F/x_j^{\,d}$.
--
--   This is the surjectivity, for $d$ large, of the map from degree-$d$ forms on $\mathbb P^n_A$ to the Čech $H^0$ of $\mathcal O_Z(d)$ on the pulled-back standard cover, in the style of Serre's finiteness results for coherent sheaves on projective space (Hartshorne II.5.19 and Ex. II.5.9). It feeds the Hilbert-functor computations, being cited in the construction of covers on which the Hilbert function of a flat closed subscheme is locally constant and in the identification of geometric-fibre $H^0$ ranks with Hilbert functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion.lean

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

theorem AlgebraicGeometry.ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] :
    ∃ d₂ : ℕ, ∀ d : ℕ, d₂ ≤ d →
      ∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι),
        ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (j : Fin (n + 1)),
            (c s).val j =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j ≤ ProjSpace.pullbackChart ι j)
                ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X j ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow j d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by sorry
