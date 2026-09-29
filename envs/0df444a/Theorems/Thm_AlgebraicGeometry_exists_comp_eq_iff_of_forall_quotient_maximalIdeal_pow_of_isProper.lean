-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper
-- name    : AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/9a30dfdc-33f9-560c-a240-823faf2321d3
-- title:
--   Factorisation through closed subschemes detected on infinitesimal thickenings
-- statement:
--   Let $R$ be a noetherian local commutative ring (in a fixed universe), let $X, Z_1, Z_2$ be schemes, let $f : X \to \operatorname{Spec} R$ be a proper morphism, and let $\iota_1 : Z_1 \to X$ and $\iota_2 : Z_2 \to X$ be closed immersions. Assume that the fibre of $\iota_2$ followed by $f$ over the closed point of $\operatorname{Spec} R$ is finite, i.e. the preimage under the underlying continuous map of $f \circ \iota_2$ of the singleton consisting of the maximal ideal of $R$ is a finite set. Assume furthermore that for every $k \in \mathbb{N}$, every commutative ring $R''$ and every morphism $\psi : \operatorname{Spec} R'' \to X$ such that $\psi$ followed by $f$ factors through the closed immersion $\operatorname{Spec}(R/\mathfrak{m}^{k+1}) \to \operatorname{Spec} R$ (that is, there is $t : \operatorname{Spec} R'' \to \operatorname{Spec}(R/\mathfrak{m}^{k+1})$ with $t$ followed by the map induced by the quotient map equal to $f \circ \psi$), the morphism $\psi$ factors through $\iota_1$ if and only if it factors through $\iota_2$. Then for every commutative ring $R'$ and every morphism $\psi : \operatorname{Spec} R' \to X$, $\psi$ factors through $\iota_1$ if and only if it factors through $\iota_2$; no finiteness, noetherian or local hypothesis is imposed on $R''$ or $R'$.
--
--   This is a rigidity statement of the Grothendieck existence/formal-functions type: for two closed subschemes of a scheme proper over a noetherian local ring, one with finite special fibre, agreement of the functors of points on all $R$-algebras killed by a power of the maximal ideal forces agreement on all affine test schemes. It is applied in the construction of fake elliptic curves in the Čerednik–Drinfeld setting, where the two closed subschemes are the kernel of a torsion subgroup scheme and a two-torsion locus, compared over infinitesimal thickenings of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X Z₁ Z₂ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (ι₁ : Z₁ ⟶ X) (ι₂ : Z₂ ⟶ X) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (hfin : ((ι₂ ≫ f).base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite)
    (h : ∀ (k : ℕ) (R'' : Type u) [CommRing R''] (ψ : Spec (CommRingCat.of R'') ⟶ X),
      (∃ t : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))),
          t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))) = ψ ≫ f) →
        ((∃ ψ₁ : Spec (CommRingCat.of R'') ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R'') ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)))
    (R' : Type u) [CommRing R'] (ψ : Spec (CommRingCat.of R') ⟶ X) :
    (∃ ψ₁ : Spec (CommRingCat.of R') ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R') ⟶ Z₂, ψ₂ ≫ ι₂ = ψ) := by sorry
