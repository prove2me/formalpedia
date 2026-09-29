-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_transfer_swap
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_transfer_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/b5afb80b-8f90-53d5-ada8-e3682fccf562
-- title:
--   Two-prime switch: the two iterated quotients agree
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order (it contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$, and is finitely generated), a nonzero natural number $N$, and two distinct primes $\ell \neq \ell'$. Let $E, E_1, E_1', d, d'$ be fake elliptic curves of level $N$ with $\Lambda$-action over $\overline{\mathbb{Q}}$ (each given by a scheme with a structure morphism to $\operatorname{Spec}\overline{\mathbb{Q}}$, a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base, and a level structure $\mathrm{lev}$), and let $K$ be an extra level of $E$ for $\ell$ and $K'$ an extra level of $E$ for $\ell'$. Assume given $\varphi : E.A \to E_1.A$ and $\psi : E_1.A \to E.A$ over the base which are homomorphisms for the group laws on $T$-points, commute with the $\Lambda$-actions in the sense $E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $E_1.\mathrm{act}\,x$ (and symmetrically for $\psi$), satisfy, whenever $\ell \in \Lambda$, that the two composites are the actions of $\ell$ on $E$ and on $E_1$, have kernel on $T$-points exactly the points factoring through $K$, and carry points factoring through $E.\mathrm{lev}$ to points factoring through $E_1.\mathrm{lev}$; and likewise $\varphi' : E.A \to E_1'.A$, $\psi'$, with $\ell'$ and $K'$ in place of $\ell$ and $K$. Assume further an extra level $K_1'$ of $E_1$ for $\ell'$ whose $\overline{\mathbb{Q}}$-points (points over the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$) are exactly the $\varphi$-images of the $\overline{\mathbb{Q}}$-points of $K'$, and an extra level $K_1$ of $E_1'$ for $\ell$ whose $\overline{\mathbb{Q}}$-points are exactly the $\varphi'$-images of those of $K$. Finally assume $d$ is an $\ell'$-level-isogeny quotient of $(E_1,K_1')$ and $d'$ an $\ell$-level-isogeny quotient of $(E_1',K_1)$. Then $d$ and $d'$ are isomorphic as fake elliptic curves: there is an isomorphism $d.A \cong d'.A$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ which is a homomorphism for the group laws on $T$-points, commutes with the $\Lambda$-actions, and identifies the level structures, a point factoring through $d.\mathrm{lev}$ if and only if its image factors through $d'.\mathrm{lev}$.
--
--   This is the second half of the two-prime switch for fake elliptic curves: the two ways of dividing $E$ successively by an $\ell$-level and an $\ell'$-level, in either order, produce isomorphic quotients, both being $E/(K \oplus K')$. It is used in establishing the commutation of the Hecke correspondences on the quaternionic moduli tower, via [`CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_two_mul_dvd_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_transfer_swap.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_transfer_swap
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (hℓℓ' : ℓ ≠ ℓ')
    (E E₁ E₁' d d' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K : E.ExtraLevel ℓ) (K' : E.ExtraLevel ℓ')

    (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφmul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁.f),
      mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) (hφact' : ∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x)
    (hφcomp : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hφker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P)
    (hφlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P))

    (φ' : E.A ⟶ E₁'.A) (hφ' : φ' ≫ E₁'.f = E.f) (ψ' : E₁'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E₁'.f)
    (hφ'mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ' hφ' (E.L.mul t P Q) = E₁'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (hφ'mul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁'.f),
      mapPt ψ' hψ' (E₁'.L.mul t P Q) = E.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q))
    (hφ'act : ∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E₁'.act x) (hφ'act' : ∀ x : ↥Λ, E₁'.act x ≫ ψ' = ψ' ≫ E.act x)
    (hφ'comp : ∀ hℓ : ((ℓ' : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ' ≫ ψ' = E.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ' ≫ φ' = E₁'.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hφ'ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt φ' hφ' P = E₁'.L.one t ↔ FactorsThrough K'.levK P)
    (hφ'lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁'.lev (mapPt φ' hφ' P))

    (K₁' : E₁.ExtraLevel ℓ')
    (hK₁' : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
      FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x)
    (K₁ : E₁'.ExtraLevel ℓ)
    (hK₁ : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁'.f,
      FactorsThrough K₁.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K.levK y ∧ mapPt φ' hφ' y = x)

    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ' (⟨E₁, K₁'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ' (AlgebraicClosure ℚ)) d)
    (hd' : FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E₁', K₁⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d') :
    FakeEllipticCurve.Iso d d' := by sorry
