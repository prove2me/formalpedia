-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_transfer_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0486abc4-bc47-5451-b701-9d8d0c670466
-- title:
--   Transfer of ℓ'-extra levels along an ℓ-isogeny
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, and distinct primes $\ell,\ell'$. Let $E,E_1$ be fake elliptic curves of type $(\Lambda,N)$ over $S$ (each consisting of a scheme with a structure morphism to $\operatorname{Spec} S$, a commutative relative group law, an abelian-scheme property bundle, fibres of dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ compatible with the group law and with a trace condition, and a level datum $\mathrm{lev}$), and let $K$ be an extra level at $\ell$ on $E$ (a closed subscheme $K.\mathrm{levK}$ of $E.A$ whose $T$-points are a subgroup killed by $\ell$, stable under $\Lambda$, meeting $E.\mathrm{lev}$ only in the identity, finite flat of finite presentation of rank $\ell^2$ over $S$, with geometric fibres $(\mathbb{Z}/\ell)^2$). Assume given morphisms $\varphi : E.A \to E_1.A$ and $\psi : E_1.A \to E.A$ over $S$ which, acting on $T$-points $P \mapsto P \circ \varphi$ (respectively $P \circ \psi$) through `mapPt`, are homomorphisms for the relative group laws and commute with the $\Lambda$-actions; that, whenever the image of $\ell$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, $\varphi$ followed by $\psi$ equals $E.\mathrm{act}$ of that element and $\psi$ followed by $\varphi$ equals $E_1.\mathrm{act}$ of it; that $1 \in \Lambda$; that for all $T$ and all $t : T \to \operatorname{Spec} S$, a $T$-point $P$ of $E$ over $t$ has $\varphi$-image the identity precisely when $P$ factors through $K.\mathrm{levK}$; and that $\varphi$ carries points factoring through $E.\mathrm{lev}$ into points factoring through $E_1.\mathrm{lev}$ and every point of $E_1$ factoring through $E_1.\mathrm{lev}$ is the $\varphi$-image of such a point of $E$. Here a point $P$ over $t$ factors through a morphism $\mathrm{lev} : C \to E.A$ when $P$ is $P_0$ followed by $\mathrm{lev}$ for some $P_0 : T \to C$. The conclusion is a conjunction of three assertions: first, every extra level $K'$ at $\ell'$ on $E$ has an extra level $K_1'$ at $\ell'$ on $E_1$ whose points, over every base $t : T \to \operatorname{Spec} S$, are exactly the $\varphi$-images of points of $K'$; second, every extra level $K_1'$ at $\ell'$ on $E_1$ arises in this way from some extra level $K'$ at $\ell'$ on $E$, but with the characterisation asserted only for points over the identity of $\operatorname{Spec} S$; third, two extra levels $K',K''$ at $\ell'$ on $E$ have the same $S$-points (over the identity of $\operatorname{Spec} S$) if and only if their sets of $\varphi$-images of $S$-points agree.
--
--   This is the transfer of extra level structures at a prime $\ell'$ along an isogeny of degree a power of the other prime $\ell$, the bookkeeping underlying the two-prime switch on the relevant moduli tower. It is used in the proof that the correspondence on the moduli tower commutes, in [`CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_two_mul_dvd_of_squarefree); note that the second and third clauses are asserted only for points over $\operatorname{Spec} S$ itself, whereas the first holds over an arbitrary base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_transfer_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (hℓℓ' : ℓ ≠ ℓ')
    (E E₁ : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ)
    (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) (hψact : ∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x)
    (hφψ : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P))
    (hlev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E₁.f),
      FactorsThrough E₁.lev x → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = x) :

    (∀ K' : E.ExtraLevel ℓ', ∃ K₁' : E₁.ExtraLevel ℓ',
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E₁.f),
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver t E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧

    (∀ K₁' : E₁.ExtraLevel ℓ', ∃ K' : E.ExtraLevel ℓ',
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧

    (∀ K' K'' : E.ExtraLevel ℓ',
      (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ↔ FactorsThrough K''.levK y) ↔
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
          (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ↔
          (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K''.levK y ∧ mapPt φ hφ y = x))) := by sorry
