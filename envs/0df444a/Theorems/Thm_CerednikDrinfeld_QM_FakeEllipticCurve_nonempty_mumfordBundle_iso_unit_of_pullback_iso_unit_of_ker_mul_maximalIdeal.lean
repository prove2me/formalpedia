-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/411544fc-051c-5e5c-9afa-fa47f136938f
-- title:
--   Triviality of the Mumford bundle over a small thickening
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0 < a$ or $0 < b$, and for each finite place $v$ of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ divides $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order, and maximal among orders containing it), let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Fix $N \in \mathbb{N}$, a commutative ring $S$ and a fake elliptic curve $E$ over $S$ with level data $(\Lambda, N)$, given by a structure morphism $E.f : A \to \operatorname{Spec} S$ carrying a commutative relative group law, an abelian-scheme property bundle, fibres of dimension $2$ and a $\Lambda$-action. Let $R_1$ be a local noetherian $S$-algebra, $R_0$ a nontrivial $S$-algebra, and $\varphi : R_1 \to R_0$ a surjective $S$-algebra map such that every element of $\ker \varphi$ annihilates every element of the maximal ideal of $R_1$. Write $A_i$ for the fibre product of $E.f$ with $\operatorname{Spec} R_i \to \operatorname{Spec} S$, and let $t : A_0 \to A_1$ commute with the projections to $A$ and cover $\operatorname{Spec}\varphi$ on the second factor. Let $L_1$, $L_0$ be relative group laws on $A_i \to \operatorname{Spec} R_i$ whose multiplication is compatible, via the projection to $A$, with the group law $E.L$. Finally let $d$ be an invertible module on $A_1$ (locally isomorphic to the unit) whose pullback along $t$ is isomorphic to the unit. Then the Mumford bundle of $d$ for $L_1$, namely $m^{*}d \otimes (p_1^{*}d^{\vee} \otimes p_2^{*}d^{\vee})$ on $A_1 \times_{R_1} A_1$, is isomorphic to the unit object.
--
--   This is the square-zero (small extension) step in the analysis of Mumford's bundle $\Lambda(d) = m^{*}d \otimes p_1^{*}d^{\vee} \otimes p_2^{*}d^{\vee}$: a line bundle on a fake elliptic curve over $R_1$ that becomes trivial on the closed thickening has trivial Mumford bundle, so it induces the trivial homomorphism to the dual abelian scheme. It is used in the construction of canonical polarisation data on fake elliptic curves over artinian base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_mumfordBundle_iso_unit_of_pullback_iso_unit_of_ker_mul_maximalIdeal
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
    (d : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules) (hd : Scheme.Modules.IsInvertible d) (hd₀ : Nonempty ((Scheme.Modules.pullback t).obj d ≅ 𝟙_ _)) :
    Nonempty (mumfordBundle (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁ d ≅ 𝟙_ _) := by sorry
