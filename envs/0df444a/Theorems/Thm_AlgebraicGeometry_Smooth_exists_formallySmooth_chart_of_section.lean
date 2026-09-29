-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section
-- name    : AlgebraicGeometry.Smooth.exists_formallySmooth_chart_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/95d9afda-2a2e-501e-aecc-286097200b38
-- title:
--   Formally smooth affine chart along a section of a smooth morphism
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} R$ a smooth morphism and $s : \operatorname{Spec} R \to A$ a morphism with $s$ followed by $f$ the identity, i.e. a section of $f$. The assertion is that there are an $n \in \mathbb{N}$ and elements $a_0,\dots,a_{n-1} \in R$ whose span is the unit ideal, such that for each index $i$ and each commutative $R$-algebra $R_i$ that is a localisation of $R$ away from $a_i$ there exist $g \in \mathbb{N}$, a commutative $R_i$-algebra $B$ which is formally smooth over $R_i$, an $R_i$-algebra homomorphism $\varepsilon : B \to R_i$, elements $x_0,\dots,x_{g-1} \in B$, and for every commutative $R_i$-algebra $C$ a map $\iota_C$ sending an $R_i$-algebra homomorphism $B \to C$ to a pair consisting of a morphism $\operatorname{Spec} C \to A$ together with a proof that it followed by $f$ equals $\operatorname{Spec}$ of the composite $R \to R_i \to C$, subject to the following. Each $x_j$ lies in $\ker \varepsilon$; $\ker\varepsilon$ is contained in the span of the $x_j$ plus $(\ker\varepsilon)^2$; if $\sum_j c_j x_j \in (\ker\varepsilon)^2$ for $c : \mathrm{Fin}\,g \to R_i$ then $c = 0$ (so the $x_j$ form a basis of $\ker\varepsilon/(\ker\varepsilon)^2$); for $\psi : C \to C'$ and $\varphi : B \to C$ the underlying morphism of $\iota_{C'}(\psi \circ \varphi)$ is $\operatorname{Spec}\psi$ followed by that of $\iota_C(\varphi)$; each $\iota_C$ is injective; the underlying morphism of $\iota_{R_i}(\varepsilon)$ is $\operatorname{Spec}(R \to R_i)$ followed by $s$; and for every commutative $R_i$-algebra $C$, every nilpotent ideal $J \subseteq C$, every $P$ in the above set of morphisms $\operatorname{Spec} C \to A$ over $\operatorname{Spec} R$ and every $\varphi_0 : B \to C/J$ whose associated morphism equals $\operatorname{Spec}$ of the quotient map followed by the morphism underlying $P$, there is $\varphi : B \to C$ with $\iota_C(\varphi) = P$.
--
--   This packages the local structure of a smooth morphism along a section: after a finite basic-open cover of the base, the section factors through an affine chart $\operatorname{Spec} B$ with $B$ formally smooth over the localised base and with free conormal module along the section, the chart being recognised functorially among points of $A$ and stable under infinitesimal thickenings. It is used in the construction of the multivariable formal group attached to a smooth group scheme along its unit section, via [`GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.Smooth.exists_formallySmooth_chart_of_section
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hf : Smooth f)
    (s : Spec (CommRingCat.of R) ⟶ A) (hs : s ≫ f = 𝟙 _) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (B : Type u) (_ : CommRing B) (_ : Algebra Rᵢ B) (_ : Algebra.FormallySmooth Rᵢ B)
          (ε : B →ₐ[Rᵢ] Rᵢ) (x : Fin g → B)
          (ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C],
            (B →ₐ[Rᵢ] C) →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),

          (∀ j, ε (x j) = 0) ∧
          (RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2) ∧
          (∀ c : Fin g → Rᵢ, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0) ∧

          (∀ (C C' : Type u) [CommRing C] [Algebra Rᵢ C] [CommRing C'] [Algebra Rᵢ C']
            (ψ : C →ₐ[Rᵢ] C') (φ : B →ₐ[Rᵢ] C),
              (ι C' (ψ.comp φ)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (ι C φ).1) ∧

          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], Function.Injective (ι C)) ∧

          ((ι Rᵢ ε).1 = Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) ≫ s) ∧

          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
            ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f)
              (φ₀ : B →ₐ[Rᵢ] C ⧸ J),
              (ι (C ⧸ J) φ₀).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 →
                ∃ φ : B →ₐ[Rᵢ] C, ι C φ = P) := by sorry
