-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen
-- name    : AlgebraicGeometry.exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/a43a1257-7075-57fe-bb06-104c38241263
-- title:
--   Sections of an abstract base change on preimages of affine opens
-- statement:
--   Let $K$ be a commutative ring, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} K$, and $H$ a commutative ring equipped with a $K$-algebra structure. Let $B$ be a scheme together with morphisms $f_B : B \to \operatorname{Spec} H$ and $\pi : B \to A$, and assume the square formed by $\pi$, $f_B$, $f$ and $\operatorname{Spec}$ of the structure map $K \to H$ is cartesian (`IsPullback`); the fibre product is thus given abstractly, not as Mathlib's chosen one. Each $\Gamma(A,V)$ is regarded as a $K$-algebra through the ring map obtained from the inverse of the canonical isomorphism $K \cong \Gamma(\operatorname{Spec} K, \top)$ followed by $f$ on sections over $V$, and likewise each $\Gamma(B,W)$ through $\pi$ followed by $f$. The assertion is that there exists a family of $K$-algebra isomorphisms $\varepsilon_V : \Gamma(B, \pi^{-1}V) \cong \Gamma(A,V) \otimes_K H$, indexed by the affine opens $V$ of $A$, such that: $\pi^{-1}V$ is an affine open of $B$ for every affine open $V$; $\varepsilon_V(\pi^\sharp a) = a \otimes 1$ for $a \in \Gamma(A,V)$; $\varepsilon_V$ sends the image of $h \in H$ under $H \cong \Gamma(\operatorname{Spec} H, \top)$ followed by $f_B$ on sections into $\Gamma(B,\pi^{-1}V)$ to $1 \otimes h$; and, for affine opens $V' \le V$, tensoring the restriction $K$-algebra map $\Gamma(A,V) \to \Gamma(A,V')$ with the identity of $H$ carries $\varepsilon_V(s)$ to $\varepsilon_{V'}$ of the restriction of $s$ from $\pi^{-1}V$ to $\pi^{-1}V'$.
--
--   This is the standard description of a base change along $\operatorname{Spec} H \to \operatorname{Spec} K$ on sections over preimages of affine opens, $\Gamma(B,\pi^{-1}V) \cong \Gamma(A,V)\otimes_K H$, stated for an arbitrary cartesian square so that it applies to fibre products presented only through their universal property. It is the version used in the study of presheaves of modules under flat base change, where the compatibility with restriction along $V' \le V$ is what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    {B : Scheme.{u}} (fB : B ⟶ Spec (CommRingCat.of H)) (π : B ⟶ A)
    (hB : IsPullback π fB f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKB : ∀ W : B.Opens, Algebra K Γ(B, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom (π ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ(B, π ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
      (∀ (V : A.Opens) (hV : IsAffineOpen V), IsAffineOpen (π ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)), ε V hV ((π.app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV ((fB.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
            (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (s : Γ(B, π ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
            ε V' hV' ((B.presheaf.map (homOfLE (π.preimage_mono hle)).op).hom s)) := by sorry
