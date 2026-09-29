-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/596bb54c-e5d5-5d0b-8ee7-2b00093b702b
-- title:
--   Residues at boundary sections vanish on Čech coboundaries
-- statement:
--   Let $k$ be a perfect field and $X$ an integral scheme, let $\mathcal V$ consist of two affine opens $U_0,U_1$ of $X$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine, and let $c\colon X\to\operatorname{Spec} k$ be proper and smooth of relative dimension $1$. Write $\mathcal U=\mathcal V.\mathrm{cover}\ c$ for the associated two-chart datum over $k$, with $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\sqcap U_1)$, the $k$-algebra structures coming from $c$, and $\rho_0,\rho_1$ the restriction maps. Let $\sigma\colon\iota\to(\operatorname{Spec} k\to X)$ be a finite family which is sectional for $\mathcal V$ and $c$: each $\sigma_i$ is a section of $c$, each has image inside $U_0$, the images are pairwise disjoint, and their union is the complement of $U_1$. Let $\Lambda_i$ be Laurent charts of $\mathcal U$, i.e. ring homomorphisms $A_{01}\to k(\!(t)\!)$ carrying $a\in k$ to the constant series $a$, such that each $\Lambda_i$ is a completion along $\rho_0$ relative to the evaluation map $A_0\to k$ attached to $\sigma_i$ — expansions of elements of $A_0$ are power series, every truncation of a power series is realised by some element of $A_0$, and the vanishing of the first $n$ coefficients of $b\in A_0$ is equivalent to $b$ lying in the $n$-th power of the kernel of that evaluation map — and such that each $\Lambda_i$ has a parameter along $\rho_0$, i.e. some element of $A_0$ expands to $t$. The conclusion is that the residues of the family vanish on Čech coboundaries: the range of the Čech differential $(\omega_0,\omega_1)\mapsto-\,r_0\omega_0+r_1\omega_1$ from $\Omega_{A_0/k}\times\Omega_{A_1/k}$ to $\Omega_{A_{01}/k}$, with $r_0,r_1$ induced by $\rho_0,\rho_1$, is contained in the kernel of $\eta\mapsto\sum_{i}\operatorname{Res}_{\Lambda_i}(\eta)$.
--
--   This is the residue-theorem input making the chart-residue Serre pairing of a two-chart cover well defined on $\check H^1(\mathcal V,\Omega^1)$, for the charts sitting at the points of $X\setminus U_1$. It is used by the corresponding statements for the cover coming from a finite-map datum on a smooth proper curve, and thence in the construction of the integral Serre pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type v} [Fintype ι] (σ : ι → (Spec (.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0) :
    (𝒱.cover c).ResiduesVanishOnCoboundaries Λ := by sorry
