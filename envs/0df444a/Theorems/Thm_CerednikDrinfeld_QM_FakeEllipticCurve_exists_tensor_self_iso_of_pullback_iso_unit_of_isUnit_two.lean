-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tensor_self_iso_of_pullback_iso_unit_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_tensor_self_iso_of_pullback_iso_unit_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/01aa49da-95a3-5a26-8da1-0249636d505f
-- title:
--   Halving an invertible module trivial along a small extension
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ be such that $\mathrm{IsIndefiniteRamifiedExactlyAt}$ holds, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order and is maximal among orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\mathrm{star} \colon \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$. Fix $N \in \mathbb{N}$, a commutative ring $S$ and a fake elliptic curve $E$ of level $N$ over $S$ for $\Lambda$, with structure morphism $E.f \colon E.A \to \operatorname{Spec} S$. Let $R_1$ be a local noetherian commutative ring and $R_0$ a nontrivial commutative ring, both $S$-algebras, and let $\varphi \colon R_1 \to R_0$ be a surjective $S$-algebra map whose kernel is annihilated by the maximal ideal of $R_1$, in the sense that $xm = 0$ for all $x \in \ker \varphi$ and $m \in \mathfrak{m}_{R_1}$. Write $A_i$ for the fibre product of $E.f$ with $\operatorname{Spec} R_i \to \operatorname{Spec} S$. Let $t \colon A_0 \to A_1$ be a morphism compatible with the projections to $E.A$ and with the projections to the bases via $\operatorname{Spec} \varphi$. Assume given relative group laws $L_1$ on $A_1 \to \operatorname{Spec} R_1$ and $L_0$ on $A_0 \to \operatorname{Spec} R_0$ whose multiplications are compatible, after composing with the projection to $E.A$, with that of $E.L$ on points over arbitrary test schemes, and assume $2$ is a unit in $R_1$. Then for every invertible module $d$ on $A_1$ admitting an isomorphism $t^* d \cong \mathcal{O}_{A_0}$ (the monoidal unit) there exists an invertible module $d'$ on $A_1$ with $t^* d' \cong \mathcal{O}_{A_0}$ and $d' \otimes d' \cong d$.
--
--   This is the halving step in the deformation theory of line bundles along a small extension $R_1 \twoheadrightarrow R_0$ of the base of a fake elliptic curve: invertible modules on $A_1$ trivialised on $A_0$ are classified additively by Čech deformation cocycles with values in a vector space over the residue field, so invertibility of $2$ lets such a class be halved. It is used in the symmetrisation of line bundles on base-changed fake elliptic curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isSymmetric_pullback_iso_of_isSymmetric_of_pullback_iso_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tensor_self_iso_of_pullback_iso_unit_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tensor_self_iso_of_pullback_iso_unit_of_isUnit_two
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
    ∃ d' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules,
      Scheme.Modules.IsInvertible d' ∧ Nonempty ((Scheme.Modules.pullback t).obj d' ≅ 𝟙_ _) ∧ Nonempty (d' ⊗ d' ≅ d) := by sorry
