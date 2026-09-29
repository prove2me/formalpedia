-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/d361735b-8538-504d-8811-798fb2a86520
-- title:
--   Base change of Atkin–Lehner quotients with extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell,r$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$. Let $v,v_1$ be objects of `QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S`, i.e. pairs consisting of a fake elliptic curve over $S$ (an abelian scheme of relative dimension $2$ with commutative relative group law, $\Lambda$-action satisfying the trace condition, and level-$N$ datum $\mathrm{lev}$) together with an extra level structure at $\ell$, given by a closed immersion $\mathrm{lev}_K : K \to A$ that is a finite flat subgroup of rank $\ell^{2}$, $\Lambda$-stable, $\ell$-torsion and disjoint from $\mathrm{lev}$; let $v',v_1'$ be such objects over $S'$. Assume for each of the pairs $(v',v)$ and $(v_1',v_1)$ that there is a morphism $g$ from the $S'$-curve to the $S$-curve making a pullback square over $\operatorname{Spec}\varphi$, compatible with the group laws on $T$-points, commuting with the $\Lambda$-actions, and carrying $T$-points factoring through the level-$N$ datum, resp. through the extra level $K$, of the $S'$-object to points factoring through the corresponding datum of the $S$-object after composing with $g$; this is the project's `FakeEllipticCurve.IsPullback` for $\varphi$ together with the extra-level clause. Then if $v_1$ is an Atkin–Lehner quotient of $v$ at $r$ in the project's sense for `WithExtraLevel` — there are morphisms $\phi$, $\psi$ over $S$ in the two directions, both homomorphisms for the relative group laws on $T$-points and both commuting with the $\Lambda$-actions, with $\phi\psi$ and $\psi\phi$ equal to the action of $r$ whenever $r \in \Lambda$, with the kernel of $\phi$ on $T$-points described as those $P$ killed by every $m \in \Lambda$ with $m\,\bar m = rn$ for some $n \in \mathbb{Z}$, and with $\phi$ carrying points factoring through $\mathrm{lev}$, resp. through $K$, into the corresponding data of $v_1$ — then the same holds for $v'$ and $v_1'$ over $S'$ at the same $r$.
--
--   This is the descent of the Atkin–Lehner quotient relation along base change at the level of the moduli problem of fake elliptic curves with an auxiliary level structure at $\ell$, the upper floor of the corresponding statement without extra level. It is used to propagate the Atkin–Lehner data through the Čerednik–Drinfeld moduli tower, notably in the verification of the tower laws and in the converse comparison between pullbacks and Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (r : ℕ)
    (v v₁ : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (v' v₁' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (hv : (∃ (g : v'.1.A ⟶ v.1.A)
        (hg : CategoryTheory.IsPullback g v'.1.f v.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' v'.1.f),
        (v'.1.L.mul t' Q Q').1 ≫ g =
          (v.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, v'.1.act x ≫ g = g ≫ v.1.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' v'.1.f),
        (QM.FactorsThrough v'.1.lev Q → ∃ Q₀ : T ⟶ v.1.C, Q₀ ≫ v.1.lev = Q.1 ≫ g) ∧
        (QM.FactorsThrough v'.2.levK Q → ∃ Q₀ : T ⟶ v.2.K, Q₀ ≫ v.2.levK = Q.1 ≫ g))))
    (hv₁ : (∃ (g : v₁'.1.A ⟶ v₁.1.A)
        (hg : CategoryTheory.IsPullback g v₁'.1.f v₁.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' v₁'.1.f),
        (v₁'.1.L.mul t' Q Q').1 ≫ g =
          (v₁.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, v₁'.1.act x ≫ g = g ≫ v₁.1.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' v₁'.1.f),
        (QM.FactorsThrough v₁'.1.lev Q → ∃ Q₀ : T ⟶ v₁.1.C, Q₀ ≫ v₁.1.lev = Q.1 ≫ g) ∧
        (QM.FactorsThrough v₁'.2.levK Q → ∃ Q₀ : T ⟶ v₁.2.K, Q₀ ≫ v₁.2.levK = Q.1 ≫ g))))
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v v₁) :
    QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v' v₁' := by sorry
