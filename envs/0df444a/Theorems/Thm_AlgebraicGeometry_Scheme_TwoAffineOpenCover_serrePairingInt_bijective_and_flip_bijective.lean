-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f8af2745-0091-509a-8c33-1525ff53e549
-- title:
--   Integral Serre pairing perfect from the residue-field fibre
-- statement:
--   Let $R$ be a commutative local ring, $X$ a scheme, $c \colon X \to \operatorname{Spec} R$ a morphism, and $\mathcal V$ a two-affine open cover of $X$: opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$, both $U_i$ and $U_0 \cap U_1$ affine. Let $k$ be a field which is an $R$-algebra with $R \to k$ surjective, and let $X_k$ be the fibre product of $c$ with $\operatorname{Spec} k \to \operatorname{Spec} R$, carrying the pulled-back cover and the second projection as structure morphism. Let $\iota$ be a finite index type and $\Lambda$, $\Lambda_k$ families indexed by $\iota$ of Laurent charts, i.e. ring homomorphisms from the sections on $U_0 \cap U_1$ (respectively its preimage) to $R$-valued (respectively $k$-valued) Laurent series carrying $\operatorname{algebraMap}$ images of scalars to constant series. Assume each $\Lambda_k$-expansion of a pulled-back section is the coefficientwise reduction along $R \to k$ of the corresponding $\Lambda$-expansion; that for both covers the sum over $\iota$ of the residues kills the range of the Čech differential on Kähler sections (so the integral Serre pairings $\check H^0(\Omega^1) \times \check H^1(\mathcal O) \to R$, $\to k$ are defined); that $\check H^0$ of the Kähler sections and $\check H^1$ of the structure-sheaf sections of $\mathcal V$ over $R$ are finite free $R$-modules; that $k$-linear isomorphisms $k \otimes_R \check H^0 \cong \check H^0_k$ and $k \otimes_R \check H^1 \cong \check H^1_k$ are given which send $1 \otimes \omega$ and $1 \otimes x$ to their canonical base-change images; and that the pairing for $\Lambda_k$ and its flip are both bijective. Then the pairing for $\Lambda$ and its flip are both bijective.
--
--   This is Serre duality in perfect-pairing form for a two-chart Čech model over a local base: perfectness of the integral pairing on the total space is deduced from perfectness of the pairing on the fibre over the residue field. It is used in the construction of Laurent charts with perfect integral Serre pairing for smooth proper curves with a finite map datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u w

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {ι : Type w} [Fintype ι]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {k : Type u} [Field k] [Algebra R k] (hπ : Function.Surjective (algebraMap R k))
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (Λk : ι → ((𝒱.pullback c k).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).LaurentChart)
    (hΛ : ∀ i y, (Λk i).expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c k).map01 y) =
      ((Λ i).expand y).map (algebraMap R k))
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)
    (hvk : ((𝒱.pullback c k).cover
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).ResiduesVanishOnCoboundaries Λk)
    [Module.Free R (𝒱.kaehlerSections c).H0] [Module.Finite R (𝒱.kaehlerSections c).H0]
    [Module.Free R (𝒱.structureSheafSections c).H1] [Module.Finite R (𝒱.structureSheafSections c).H1]
    (eH0 : k ⊗[R] (𝒱.kaehlerSections c).H0 ≃ₗ[k]
      ((𝒱.pullback c k).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).H0)
    (heH0 : ∀ ω, eH0 (1 ⊗ₜ[R] ω) = Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c k ω)
    (eH1 : k ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[k]
      ((𝒱.pullback c k).structureSheafSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).H1)
    (heH1 : ∀ x, eH1 (1 ⊗ₜ[R] x) = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c k x)
    (hk : Function.Bijective (((𝒱.pullback c k).cover
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).serrePairingInt Λk hvk) ∧
      Function.Bijective (((𝒱.pullback c k).cover
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).serrePairingInt Λk hvk).flip) :
    Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv) ∧
      Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv).flip := by sorry
