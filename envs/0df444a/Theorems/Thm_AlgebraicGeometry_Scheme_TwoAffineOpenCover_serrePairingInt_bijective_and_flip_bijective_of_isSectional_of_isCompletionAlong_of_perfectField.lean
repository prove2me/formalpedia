-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9aafccb7-9280-5369-892c-566aa7a725d4
-- title:
--   Perfectness of the two-chart residue pairing on a smooth proper curve
-- statement:
--   Let $k$ be a perfect field and $X$ an integral scheme, equipped with a morphism $c \colon X \to \operatorname{Spec} k$ that is proper and smooth of relative dimension $1$. Let $\mathcal V$ consist of two affine opens $U_0, U_1 \subseteq X$ with affine intersection and $U_0 \sqcup U_1 = \top$; write $\mathcal U = \mathcal V.\mathrm{cover}\,c$ for the associated two-chart datum with $k$-algebras $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$ and the restriction maps $\rho_0, \rho_1$. Let $\iota$ be a finite index type and $\sigma \colon \iota \to \operatorname{Hom}(\operatorname{Spec} k, X)$ a family that is sectional for $c$ and $\mathcal V$: each $\sigma_i$ is a section of $c$, each image lies in $U_0$, the images are pairwise disjoint, and their union is exactly the complement of $U_1$. Let $\Lambda_i$ be Laurent charts for $\mathcal U$, i.e. ring homomorphisms $A_{01} \to k(\!(t)\!)$ carrying $\operatorname{im}(k \to A_{01})$ to constant series. Assume each $\Lambda_i$ is a completion along $\rho_0$ and the evaluation $A_0 \to k$ attached to $\sigma_i$: $\Lambda_i \circ \rho_0$ is regular, every truncated power series in $k[[t]]/(t^n)$ is realised by some element of $A_0$, and an element of $A_0$ has vanishing expansion coefficients in degrees $< n$ exactly when it lies in the $n$-th power of the kernel of the evaluation map. Assume each $\Lambda_i$ has a parameter, i.e. some $a \in A_0$ with $\Lambda_i(\rho_0 a) = t$, and assume the residue sum $\sum_i \operatorname{Res}_{\Lambda_i}$ annihilates the range of the Čech differential $(-\,r_0) \oplus r_1 \colon \Omega_{A_0/k} \times \Omega_{A_1/k} \to \Omega_{A_{01}/k}$. Then the residue pairing $\check H^0(\mathcal U, \Omega^1) \times \check H^1(\mathcal U, \mathcal O) \to k$, obtained from the cup product followed by the trace form of the residue sum, is perfect: both the map sending a class in $\check H^0$ to the resulting $k$-linear functional on $\check H^1$ and its flip are bijective.
--
--   This is Serre duality for a smooth proper curve over a perfect field, spelled out for a cover by two affine charts with residues computed in explicit Laurent expansions at the marked sections. It is the source of the duality input for the production of Laurent charts with perfect Serre pairing in [`AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional`](thm.html#AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_laurentChart_isCompletionAlong_hasParameter_serrePairingInt_bijective_of_isSectional); the vanishing of the residue sum on coboundaries is taken as a hypothesis so that the conclusion concerns the consumer's own pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective_of_isSectional_of_isCompletionAlong_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type v} [Fintype ι] (σ : ι → (Spec (.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) :
    Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv) ∧
      Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv).flip := by sorry
