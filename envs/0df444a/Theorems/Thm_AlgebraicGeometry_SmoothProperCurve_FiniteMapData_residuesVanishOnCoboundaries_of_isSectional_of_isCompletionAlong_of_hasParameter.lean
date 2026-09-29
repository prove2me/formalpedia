-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
-- name    : AlgebraicGeometry.SmoothProperCurve.FiniteMapData.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/7272dca1-6f77-56b2-bb55-23e9e41770c9
-- title:
--   Residue sums vanish on Čech coboundaries over ℤ₍ₚ₎
-- statement:
--   Let $p$ be a prime and let $R=\mathtt{ratLocalizedAt}\ p$ be the subring of $\mathbf{Q}$ of rationals whose denominator is coprime to $p$. Let $c\colon X\to\operatorname{Spec} R$ be a proper, smooth of relative dimension one, geometrically integral morphism of schemes, let $\varepsilon$ be a morphism $\operatorname{Spec} R\to X$ with $\varepsilon$ followed by $c$ the identity, and let $\mathfrak F$ be a `FiniteMapData` for $(c,\varepsilon)$: affine opens $U,V$ covering $X$ with $U$ the complement of the image of $\varepsilon$, sections $f\in\Gamma(X,U)$, $g\in\Gamma(X,V)$ whose basic opens both equal $U\cap V$ and whose restrictions there are mutually inverse, with $\Gamma(X,U)$ finite over $R[f]$, $\Gamma(X,V)$ finite over $R[g]$, and all $f$-level sets over local $R$-algebras free of one fixed rank $m$. Its two-chart cover is $U_0=V$, $U_1=U$, giving $A_0=\Gamma(X,V)$, $A_1=\Gamma(X,U)$, $A_{01}=\Gamma(X,V\cap U)$ with the restriction $R$-algebra maps $\rho_0,\rho_1$. Let $\iota$ be finite and $\sigma\colon\iota\to(\operatorname{Spec} R\to X)$ be such that the cover is sectional for $\sigma$: each $\sigma_i$ is a section of $c$ with image in $V$, the complement of $U$ is the union of the images, and the images are pairwise disjoint. Let $\Lambda_i$ be Laurent charts, i.e. ring homomorphisms $\Gamma(X,V\cap U)\to R(\!(t)\!)$ carrying $R$ to constant series, such that each $\Lambda_i$ is a completion along $\rho_0$ and the $R$-algebra map $e_i\colon\Gamma(X,V)\to R$ induced by $\sigma_i$ — so `IsRegular` holds for $\rho_0$, every power series is matched to any prescribed finite order by the expansion of some element of $\Gamma(X,V)$, and the expansion of $b$ has vanishing coefficients in degrees $<n$ exactly when $b\in(\ker e_i)^n$ — and such that each $\Lambda_i$ has a parameter along $\rho_0$, i.e. some $b\in\Gamma(X,V)$ expands to $t$. Then the family $(\Lambda_i)$ satisfies `ResiduesVanishOnCoboundaries`: the image of the Čech differential on Kähler differentials $\Omega_{\Gamma(X,V)/R}\oplus\Omega_{\Gamma(X,U)/R}\to\Omega_{\Gamma(X,V\cap U)/R}$ lies in the kernel of the total residue map $\eta\mapsto\sum_{i}\operatorname{Res}_{\Lambda_i}\eta$.
--
--   This is the residue theorem (sum of residues of a rational differential is zero) in the integral form needed for the two-chart Čech model of Serre duality on a smooth proper curve over $\mathbf{Z}_{(p)}$. It supplies the vanishing hypothesis in the construction of the integral Serre pairing attached to a finite-map chart datum, `exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (ι : Type) [Fintype ι] (σ : ι → (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) ⟶ X))
    (hσ : 𝔉.twoAffineOpenCover.IsSectional c σ)
    (Λ : ι → (𝔉.twoAffineOpenCover.cover c).LaurentChart)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝔉.twoAffineOpenCover.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝔉.twoAffineOpenCover.cover c).ρ0) :
    (𝔉.twoAffineOpenCover.cover c).ResiduesVanishOnCoboundaries Λ := by sorry
