-- Prove2me | Theorems.Thm_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt
-- name    : ArtinL.eulerFactor_eq_charpolyRev_restrict_arithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/b7f32ee7-9770-5316-a3de-dadf1f63d970
-- title:
--   Artin Euler factor computed at a finite Galois level
-- statement:
--   Fix $n \in \mathbb{N}$ and a group homomorphism $\rho \colon \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to \mathrm{GL}_n(\mathbb{C})$, where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is a number field and Galois over $\mathbb{Q}$, and let $\rho_F \colon (F \simeq_{\mathbb{Q}} F) \to \mathrm{GL}_n(\mathbb{C})$ be a homomorphism with $\rho = \rho_F \circ \mathrm{res}_F$, restriction along `AlgEquiv.restrictNormalHom F`. Let $p$ be a prime, and let $P$ be a maximal ideal of $\mathcal{O}_F$ lying over the ideal $(p) \subseteq \mathbb{Z}$. Write $V = \mathbb{C}^n$ with the $\mathrm{Gal}(F/\mathbb{Q})$-action [`Deformation.matrixRepresentation ρF`](def/Deformations_MatrixRepresentation.html#L15) obtained from $\rho_F$ by viewing invertible matrices as linear automorphisms, and let $V^{I_P}$ be the invariants of the restriction of this action to the inertia subgroup `P.inertia (F ≃ₐ[ℚ] F)`. The assertion is a dependent pair: first, the arithmetic Frobenius $\mathrm{Frob}_P =$ `arithFrobAt ℤ (F ≃ₐ[ℚ] F) P` acts on $V$ preserving $V^{I_P}$; and second, granted that, the Euler factor $\rho$ at $p$ equals the reversed characteristic polynomial, i.e. $\det(1 - X \rho_F(\mathrm{Frob}_P))$ computed in a basis of $V^{I_P}$, of the endomorphism of $V^{I_P}$ induced by $\rho_F(\mathrm{Frob}_P)$. Here [`ArtinL.eulerFactor ρ p`](def/ArtinL_EulerFactor.html#L86) is defined by choosing, if one exists, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits together with $\sigma$ in the decomposition subgroup of $A$ over $\mathbb{Q}$ inducing $x \mapsto x^p$ on the residue field of $A$, and taking the reversed characteristic polynomial of $\sigma$ on the subspace [`ArtinL.inertiaInvariants ρ A`](def/ArtinL_EulerFactor.html#L71) when $\sigma$ preserves it, and $1$ in all degenerate cases.
--
--   This is the standard comparison showing that the local factor of an Artin $L$-function at $p$, defined through a place of $\overline{\mathbb{Q}}$ above $p$, may be computed in any finite Galois subextension through which the representation factors and at any prime of that subextension above $p$. It is used in the identification of Euler factors with local traces in [`ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.eulerFactor_eq_charpolyRev_restrict_arithFrobAt {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ h : ∀ w ∈ Representation.invariants
        ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P) w ∈
        Representation.invariants
          ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      ArtinL.eulerFactor ρ p =
        ArtinL.charpolyRev
          ((Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)).restrict h) := by sorry
