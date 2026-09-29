-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/4bfaefee-a57f-51f5-ad4f-9509dfd643c2
-- title:
--   Partner of a level-ℓ isogeny with a rational kernel point
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $k$ be an algebraically closed field, $\ell$ a prime with $k$ of characteristic $\ell$ and $\ell \nmid N$, and assume: $\Lambda$ is a maximal order (an order, maximal among the orders containing it); $q,q'$ are primes such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every $v$ in the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q \in v$ or $q' \in v$; and $\ell \neq q$, $\ell \neq q'$. Let $E$, $E_\ell$ be fake elliptic curves for $(\Lambda,N)$ over $k$ together with Frobenius–Verschiebung data $D$ for $\ell$ relating them, let $K$ be an extra level of $E$ at $\ell$ (a closed immersion $K \to E.A$ whose points form a $\Lambda$-stable subgroup of $\ell$-torsion, finite flat of rank $\ell^2$ over the base and meeting the level structure $E.\mathrm{lev}$ only in the identity), and let $d$ be a further fake elliptic curve for $(\Lambda,N)$ over $k$. Suppose given morphisms $\varphi : E.A \to d.A$ and $\psi : d.A \to E.A$ over $\operatorname{Spec} k$ such that, for every $k$-scheme $T \to \operatorname{Spec} k$, composition with $\varphi$ (respectively $\psi$) is a homomorphism for the relative group laws on $T$-points, both commute with the $\Lambda$-actions ($E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $d.\mathrm{act}\,x$, and symmetrically for $\psi$), and, whenever $\ell \in \Lambda$, $\varphi$ followed by $\psi$ is $E.\mathrm{act}\,\ell$ and $\psi$ followed by $\varphi$ is $d.\mathrm{act}\,\ell$. Suppose moreover that for all $T$-points $P$ of $E$ the image $P \circ \varphi$ is the identity section of $d$ if and only if $P$ factors through $K$, that $\varphi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $d.\mathrm{lev}$, and that there is a $k$-point of $E$ (a section over $\mathrm{id}_{\operatorname{Spec} k}$) which factors through $K$ and differs from the identity. Then every $k$-point $Q$ of $d$ with $Q \circ \psi$ equal to the identity section of $E$ is itself the identity section of $d$.
--
--   This is the separable, ordinary half of the characteristic-$\ell$ dichotomy for isogenies of fake elliptic curves: if the kernel of a level-$\ell$ isogeny $\varphi$ has a non-trivial rational point, then the kernel of its partner $\psi$ has none, so that $\psi$ is inseparable. It is used in the construction of Frobenius–Verschiebung data for such an isogeny, a step in the Eichler–Shimura congruence relation for Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) (d : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f) (ψ : d.A ⟶ E.A) (hψ : ψ ≫ E.f = d.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t d.f),
      mapPt ψ hψ (d.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) (hψact : ∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ E.act x)
    (hcomp : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough K.levK P)
    (hlev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough d.lev (mapPt φ hφ P))
    (hK : ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      FactorsThrough K.levK P ∧ P ≠ E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) d.f,
      mapPt ψ hψ Q = E.L.one (𝟙 (Spec (CommRingCat.of k))) → Q = d.L.one (𝟙 (Spec (CommRingCat.of k))) := by sorry
