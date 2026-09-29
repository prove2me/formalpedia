-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/c790130f-7d6f-53f9-97a4-83cfc07af450
-- title:
--   Triviality of d⊗[-1]^*d along a small thickening
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every $v$ in the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Fix $N\in\mathbb{N}$, a commutative ring $S$ and a fake elliptic curve $E$ over $S$ of level $N$ with $\Lambda$-action, with structure morphism $E.f\colon A\to\operatorname{Spec}S$ and commutative relative group law $E.L$. Let $R_1$ be a local noetherian $S$-algebra, $R_0$ a nontrivial $S$-algebra, and $\varphi\colon R_1\to R_0$ a surjective $S$-algebra map whose kernel annihilates the maximal ideal of $R_1$ (i.e. $xm=0$ for $x\in\ker\varphi$, $m\in\mathfrak{m}_{R_1}$). Write $A_i$ for the fibre product of $E.f$ with $\operatorname{Spec}R_i\to\operatorname{Spec}S$, and let $t\colon A_0\to A_1$ be a morphism compatible with the first projections and with the second projections via $\operatorname{Spec}\varphi$. Let $L_1$, resp. $L_0$, be relative group laws on $A_1$ over $R_1$, resp. $A_0$ over $R_0$, each compatible with $E.L$ in the sense that the first projection carries the product of two points to the product of their images. Assume $2$ is a unit in $R_1$. Then for every module $d$ on $A_1$ that is invertible (each point has a neighbourhood on which $d$ pulls back to the unit sheaf) and whose pullback along $t$ is isomorphic to the monoidal unit, the tensor product of $d$ with the pullback of $d$ along `negMor` of $L_1$ — the underlying morphism $A_1\to A_1$ of $L_1.\mathrm{inv}$ applied to the identity point — is isomorphic to the monoidal unit.
--
--   This is the statement that the inversion morphism acts by $-1$ on the kernel of $\operatorname{Pic}A_1\to\operatorname{Pic}A_0$ for a square-zero-type thickening with $2$ invertible, in the form needed for the fake elliptic curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$. It feeds the construction of symmetric line bundles on such thickenings, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two), and is obtained from the corresponding statement for abelian-scheme property bundles together with the compatibility of inversion with base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_tensor_pullback_negMor_iso_unit_of_pullback_iso_unit_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁]
    [CommRing R₀] [Nontrivial R₀] [Algebra S R₁] [Algebra S R₀]
    (φ : R₁ →ₐ[S] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)

    (t : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
    (ht₁ : t ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
    (ht₂ : t ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (L₀ : RelativeGroupLaw R₀ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
    (hL₀ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (h2 : IsUnit (2 : R₁))
    (d : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules) (hd : Scheme.Modules.IsInvertible d) (hd₀ : Nonempty ((Scheme.Modules.pullback t).obj d ≅ 𝟙_ _)) :
    Nonempty (d ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj d ≅ 𝟙_ _) := by sorry
