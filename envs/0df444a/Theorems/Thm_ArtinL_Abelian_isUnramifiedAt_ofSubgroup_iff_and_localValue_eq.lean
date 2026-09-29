-- Prove2me | Theorems.Thm_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
-- name    : ArtinL.Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/062d3271-fca9-5c02-9b69-27ac9ca81bb4
-- title:
--   Unramifiedness and local value for a character of H
-- statement:
--   Let $F$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ which is a number field and Galois over $\mathbb{Q}$, put $G=\mathrm{Gal}(F/\mathbb{Q})$, let $H\le G$ be a subgroup with fixed field $F^{H}$, and let $\chi\colon H\to\mathbb{C}^{\times}$ be a homomorphism. Let $p$ be a prime, let $Q$ be a maximal ideal of $\mathcal{O}_F$ lying over $p\mathbb{Z}$, and let $v$ be a height one prime of $\mathcal{O}_{F^{H}}$ with $Q\cap\mathcal{O}_{F^{H}}=v$. Write $\chi'=$ [`ArtinL.Abelian.ofSubgroup H χ`](def/ArtinL_Abelian.html#L94) for the character of $\mathrm{Gal}(F/F^{H})$ obtained from $\chi$ through the identification of the fixing subgroup of $F^{H}$ with $H$. Two assertions are made. First, $\chi'$ is trivial on the inertia subgroup, inside $\mathrm{Gal}(F/F^{H})$, of the chosen prime of $\mathcal{O}_F$ above $v$ if and only if $\chi(\sigma)=1$ for every $\sigma\in H$ lying in the inertia subgroup of $Q$ in $G$. Second, under that vanishing on inertia, the value $\chi'(\mathrm{Frob})$ at the arithmetic Frobenius of the chosen prime above $v$ — which is what [`ArtinL.Abelian.localValue`](def/ArtinL_Abelian.html#L36) returns in the unramified case — equals $\chi(\sigma)$ for every $\sigma\in H$ such that $\sigma^{-1}\,\mathrm{Frob}_Q^{\,f}$ lies in the inertia subgroup of $Q$ in $G$, where $\mathrm{Frob}_Q$ is the arithmetic Frobenius of $Q$ for $F/\mathbb{Q}$ and $f$ is the residue degree of $v$ over $p$.
--
--   This reconciles the two bookkeeping conventions in play: ramification and the Artin local value for the character $\chi'$ of $\mathrm{Gal}(F/F^{H})$ are defined through a chosen prime of $F$ above $v$ and its Frobenius, whereas $Q$, its inertia subgroup and its Frobenius refer to $F/\mathbb{Q}$. It is used in the computation of the inertia-averaged sum of Frobenius powers for an induced character, [`ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum`](thm.html#ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

theorem ArtinL.Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) :
    (ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) v ↔
        ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H), σ ∈ Q.inertia (F ≃ₐ[ℚ] F) → χ ⟨σ, hσ⟩ = 1) ∧
    (ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) v →
        ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H),
          σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
              Q.inertia (F ≃ₐ[ℚ] F) →
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v = ((χ ⟨σ, hσ⟩ : ℂˣ) : ℂ)) := by sorry
