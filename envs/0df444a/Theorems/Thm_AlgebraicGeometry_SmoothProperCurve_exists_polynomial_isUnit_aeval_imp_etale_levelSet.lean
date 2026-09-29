-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_polynomial_isUnit_aeval_imp_etale_levelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/84f7b659-7364-561f-97d5-d61465f99114
-- title:
--   A one-function Bertini theorem for level sets on curves
-- statement:
--   Let $R$ be a Noetherian local ring and let $c \colon C \to \operatorname{Spec} R$ be a morphism of schemes which is proper, smooth of relative dimension $1$ and geometrically integral. Suppose given a section $\varepsilon$ of $c$, that is a morphism $\varepsilon \colon \operatorname{Spec} R \to C$ with $\varepsilon$ followed by $c$ equal to the identity, and an open $U_0 \subseteq C$ which is affine and whose points are exactly those lying outside the image of the underlying map of $\varepsilon$. Throughout, $\Gamma(C, U_0)$ carries the $R$-algebra structure coming from $c$ via the ring map $\Gamma(\operatorname{Spec} R) \to \Gamma(C,U_0)$ obtained from $c$ and the canonical identification of $R$ with the global sections of $\operatorname{Spec} R$. Let $f \in \Gamma(C,U_0)$ and let $m$ be a natural number whose image in $R$ is a unit. Assume that for every local ring $S$ which is an $R$-algebra and every $s \in S$, the level-set algebra $B_{S,s} := \bigl(S \otimes_R \Gamma(C,U_0)\bigr)/(1 \otimes f - s \otimes 1)$ is a finite free $S$-module of rank $m$. The conclusion is that there exists a polynomial $D \in R[X]$ at least one of whose coefficients is a unit, such that for every local $R$-algebra $S$ whose structure map $R \to S$ is a local homomorphism and every $s \in S$ with $D(s)$ a unit in $S$, the algebra $B_{S,s}$ is étale over $S$.
--
--   This is a one-function Bertini statement over a local base: almost all level sets of a function $f$ of degree $m$ on the affine curve $U_0$ are étale, the exceptional locus being cut out by the roots of a polynomial $D$ that is nonzero modulo the maximal ideal of $R$. It is used in the construction of relative Jacobians and of finite étale charts for smooth proper curves, and in the treatment of models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_polynomial_isUnit_aeval_imp_etale_levelSet
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀) (hε : ∀ x : C, x ∈ U₀ ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U₀)) (m : ℕ) (hm : IsUnit (m : R))
    (hls : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
        Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) = m) :
    ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
        IsUnit (Polynomial.aeval s D) →
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
        Algebra.Etale S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) := by sorry
