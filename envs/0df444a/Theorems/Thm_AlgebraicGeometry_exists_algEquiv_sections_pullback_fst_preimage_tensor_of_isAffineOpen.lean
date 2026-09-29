-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
-- name    : AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/43f0c9de-ae43-542d-8eb8-2a96cb4cc97f
-- title:
--   Sections over p₁⁻¹V as Γ(A,V)⊗_K H
-- statement:
--   Let $K$ be a commutative ring, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} K$, and $H$ a $K$-algebra; set $P := A \times_{\operatorname{Spec} K} \operatorname{Spec} H$, the pullback of $f$ along $\operatorname{Spec}$ of the structure map $K \to H$, with projections $p_1 : P \to A$ and $p_2 : P \to \operatorname{Spec} H$. Every open $V \subseteq A$ carries the $K$-algebra structure on $\Gamma(A,V)$ obtained from the ring map $K \cong \Gamma(\operatorname{Spec} K, \top) \to \Gamma(A,V)$ induced by $f$ (`Scheme.TwoAffineOpenCover.algebraOfHom`), and similarly each open $W \subseteq P$ carries the $K$-algebra structure coming from $p_1$ followed by $f$. The assertion is that there is a family $\varepsilon$ assigning to each affine open $V \subseteq A$ a $K$-algebra isomorphism $\varepsilon_V : \Gamma(P, p_1^{-1}V) \xrightarrow{\sim} \Gamma(A,V) \otimes_K H$ such that: (i) $p_1^{-1}V$ is an affine open of $P$ for every affine open $V$; (ii) $\varepsilon_V(p_1^{*}a) = a \otimes 1$ for all $a \in \Gamma(A,V)$; (iii) $\varepsilon_V$ sends the image of $h \in H$ under $K \cong$ global sections of $\operatorname{Spec} H$ followed by $p_2$ on $\Gamma(P, p_1^{-1}V)$ to $1 \otimes h$; and (iv) for affine opens $V' \leq V$ and $s \in \Gamma(P, p_1^{-1}V)$, applying $\mathrm{res}^{V}_{V'} \otimes \mathrm{id}_H$ (with $\mathrm{res}^{V}_{V'}$ the presheaf restriction viewed as a $K$-algebra map, `Scheme.TwoAffineOpenCover.restrictAlgHom`) to $\varepsilon_V(s)$ gives $\varepsilon_{V'}$ of the restriction of $s$ to $p_1^{-1}V'$.
--
--   This is the standard description of a base change $A \times_{\operatorname{Spec} K} \operatorname{Spec} H$ over an affine chart: affine opens pull back to affine opens and their sections are obtained by tensoring with $H$, in a way compatible with restriction and with the two projections. It provides the chart-level coordinates used downstream in comparisons of pullbacks of schemes and of modules along base change, in particular in arguments passing to direct limits of coefficient algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V),
        Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
      (∀ (V : A.Opens) (hV : IsAffineOpen V),
          IsAffineOpen ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
          ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
          (s : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
            ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map
              (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s)) := by sorry
