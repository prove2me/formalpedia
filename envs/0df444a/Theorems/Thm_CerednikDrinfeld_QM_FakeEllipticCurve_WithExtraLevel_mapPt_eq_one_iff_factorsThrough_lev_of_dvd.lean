-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_mapPt_eq_one_iff_factorsThrough_lev_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.mapPt_eq_one_iff_factorsThrough_lev_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/649edbb4-71bb-58fe-a669-99dbc09d3c23
-- title:
--   Dual kernel equals the ℓ-torsion of the level structure
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ satisfying `IsOrder`: $1 \in \Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of the quaternion algebra, and it is finitely generated. Let $N$ be a nonzero natural number, $\ell$ a prime with $\ell \mid N$, and $k$ an algebraically closed field in which $N \neq 0$. Let $u = (E,K)$ be a term of `WithExtraLevel Λ N ℓ k`, that is a fake elliptic curve $E = u.1$ over $k$ of level $N$ with $\Lambda$-action together with an extra level structure $u.2$ of exponent $\ell$, whose closed immersion is `u.2.levK`; and let $D$ be a further fake elliptic curve of the same type. Assume given $\varphi : E.A \to D.A$ and $\psi : D.A \to E.A$ over $\operatorname{Spec} k$ (i.e. $\varphi$ followed by $D.f$ equals $E.f$, and $\psi$ followed by $E.f$ equals $D.f$) such that, for every scheme $T$ with a morphism $t : T \to \operatorname{Spec} k$, composition with $\varphi$ (resp. $\psi$) is a homomorphism for the relative group laws on $T$-points over $t$; that $\varphi$ and $\psi$ intertwine the $\Lambda$-actions ($E.\mathrm{act}(x)$ followed by $\varphi$ equals $\varphi$ followed by $D.\mathrm{act}(x)$, and symmetrically for $\psi$, for all $x \in \Lambda$); that $\psi \circ \varphi$ and $\varphi \circ \psi$ act on $T$-points as multiplication by $\ell$ in the respective group laws; that for every $T$-point $P$ of $E$ one has $\varphi(P) = 0$ if and only if $P$ factors through `u.2.levK`; and that $\varphi$ carries points factoring through `E.lev` to points factoring through `D.lev`. The conclusion is that for every $T$, every $t : T \to \operatorname{Spec} k$ and every $T$-point $Q$ of $D$ over $t$, one has $\psi(Q) = 0$ in the group law of $E$ if and only if $Q$ factors through `D.lev` and $\ell Q = 0$ in the group law of $D$.
--
--   This identifies, for a prime $\ell$ dividing the level $N$, the kernel of the dual of a level-$\ell$ isogeny of fake elliptic curves with the $\ell$-torsion of the level-$N$ structure, so that at such primes the dual kernel is determined by the target alone. It is used in the analysis of the isogeny leg of the quaternionic moduli tower, by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isogenyData_forall_mem_iff_of_levelExt`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isogenyData_forall_mem_iff_of_levelExt), `…iso_of_forall_factorsThrough_mapPt_iff_of_dvd` and `…levelExt_setOf_factorsThrough_mapPt_of_dvd`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_mapPt_eq_one_iff_factorsThrough_lev_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.mapPt_eq_one_iff_factorsThrough_lev_of_dvd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    (k : Type) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) (D : FakeEllipticCurve Λ N k)
    (φ : u.1.A ⟶ D.A) (hφ : φ ≫ D.f = u.1.f) (ψ : D.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = D.f)
    (φ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = D.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t D.f),
      mapPt ψ hψ (D.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ D.act x) (ψ_act : ∀ x : ↥Λ, D.act x ≫ ψ = ψ ≫ u.1.act x)
    (hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t D.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt D.L t ℓ Q)
    (hkerφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = D.L.one t ↔ FactorsThrough u.2.levK P)
    (φ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough D.lev (mapPt φ hφ P)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t D.f),
      mapPt ψ hψ Q = u.1.L.one t ↔ (FactorsThrough D.lev Q ∧ nsmulPt D.L t ℓ Q = D.L.one t) := by sorry
