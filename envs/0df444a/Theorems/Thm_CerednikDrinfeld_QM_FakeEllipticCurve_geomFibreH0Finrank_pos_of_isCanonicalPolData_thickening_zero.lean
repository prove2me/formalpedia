-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_geomFibreH0Finrank_pos_of_isCanonicalPolData_thickening_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.geomFibreH0Finrank_pos_of_isCanonicalPolData_thickening_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/c0b9070b-350c-5f88-84db-cca177f37f03
-- title:
--   Positivity of h⁰ on all geometric fibres from the closed fibre
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and $a,b\in\mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a commutative ring, let $E$ be a `FakeEllipticCurve Λ N S` with structure morphism $E.f$, group law $E.L$ and $\Lambda$-action $E.act$, and let $R$ be a Noetherian local commutative $S$-algebra whose residue field is algebraically closed. Write $A_R$ for the pullback of $E.f$ along $\operatorname{Spec}$ of $S\to R$ and $A_0$ for the pullback along $\operatorname{Spec}$ of $S\to R/\mathfrak{m}^{0+1}$, so that $A_0$ is the fibre over the closed point. Assume given a morphism $j_0:A_0\to A_R$ commuting with the first projections and with the second projections up to the quotient map $R\to R/\mathfrak{m}^{0+1}$; a module $\mathcal{L}$ on $A_R$ that is invertible (locally isomorphic to the unit module); a relative group law $L_0$ on $A_0$ over $R/\mathfrak{m}^{0+1}$ whose multiplication is carried by the first projection to that of $E.L$; and a module $\mathcal{N}$ on $A_0$ for which `IsCanonicalPolData` holds with respect to the structure morphism of $A_0$, the law $L_0$, the $\Lambda$-action obtained from $E.act$ by pullback, and $\mathrm{star}$: that is, $\mathcal{N}$ is invertible, symmetric (its pullback along the inversion morphism is locally on the base isomorphic to it), its kernel is $2$-torsion, there is a faithfully flat $R/\mathfrak{m}^{0+1}$-algebra over which any group law compatible with $L_0$ admits an invertible module with trivial kernel whose Mumford square is locally on the base isomorphic to the pullback of $\mathcal{N}$, the geometric-fibre $h^0$ of $\mathcal{N}$ is positive over every algebraically closed field, and $\mathcal{N}$ is Rosati-compatible with the action and $\mathrm{star}$. Assume finally that $j_0^{*}\mathcal{L}\cong\mathcal{N}$. Then for every algebraically closed field $k$ and every ring homomorphism $s_k:R\to k$, the $k$-dimension of the global sections of the pullback of $\mathcal{L}$ to the fibre $A_R\times_{\operatorname{Spec} R}\operatorname{Spec} k$ is positive.
--
--   This is the step that propagates positivity of $h^0$ from the closed geometric fibre, where the polarisation datum lives, to every geometric point of the local base $R$, including those lying over the generic point; classically it rests on Mumford's vanishing theorem on abelian varieties together with cohomology and base change. It is used in the construction of canonical polarisation data on fake elliptic curves over local bases, in [`CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_isSymmetric_isCanonicalPolData_of_forall_thickening).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_geomFibreH0Finrank_pos_of_isCanonicalPolData_thickening_zero.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.geomFibreH0Finrank_pos_of_isCanonicalPolData_thickening_zero
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (j₀ : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : j₀ ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))
    (hj₂ : j₀ ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))))
    (𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (L₀ : RelativeGroupLaw (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))))
    (hL₀ : (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))
            (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))),
            (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))) =
              (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))
                ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓝 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))).Modules) (h𝓝 : CerednikDrinfeld.QM.IsCanonicalPolData (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))))) L₀
            (fun x : ↥Λ => pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))) ≫ E.act x) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))))
              (by rw [Category.assoc, E.act_over]; exact pullback.condition))
            (fun x => pullback.lift_snd _ _ _)
            star 𝓝)
    (hiso : Nonempty ((Scheme.Modules.pullback j₀).obj 𝓛 ≅ 𝓝)) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k),
      0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) 𝓛 k sk := by sorry
