-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8085ea29-cc15-5dec-a725-616d5513f8e7
-- title:
--   Geometric points of the kernel of a dual ℓ-isogeny
-- statement:
--   Let $q \neq q'$ be primes, let $a,b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (that is, $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$), and let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders under inclusion. Let $N \neq 0$ be a natural number, $\ell$ a prime distinct from $q$ and $q'$ with $\ell \nmid N$, and $k$ an algebraically closed field in which $\ell$ and $N$ are nonzero. Let $u = (E, \kappa)$ consist of a fake elliptic curve $E$ of level $N$ over $k$ together with an extra level structure $\kappa$ at $\ell$, and let $E'$ be a fake elliptic curve of level $N$ over $k$. Let $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ be morphisms over $\operatorname{Spec} k$ (i.e. $\varphi$ followed by $E'.f$ is $E.f$, and $\psi$ followed by $E.f$ is $E'.f$) such that, on points over an arbitrary $k$-scheme, composition with $\varphi$ and with $\psi$ is additive for the relative group laws $E.L$, $E'.L$; such that $E.\mathrm{act}(x)$ followed by $\varphi$ equals $\varphi$ followed by $E'.\mathrm{act}(x)$ and symmetrically for $\psi$, for all $x \in \Lambda$; such that composing a point with $\varphi$ then $\psi$ gives $\ell$-fold addition on $E$-points, and in the other order $\ell$-fold addition on $E'$-points; such that a point $P$ of $E.f$ has $\varphi \circ P$ equal to the unit section precisely when $P$ factors through the level map $\kappa.\mathrm{levK}$; and such that points factoring through $E.\mathrm{lev}$ are carried by $\varphi$ to points factoring through $E'.\mathrm{lev}$. Then for every algebraically closed field $k'$ and ring homomorphism $sk : k \to k'$ with $\ell \neq 0$ in $k'$, there is a bijection $e$ from $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ onto the set of points of $E'.f$ over the geometric point $\operatorname{Spec} k' \to \operatorname{Spec} k$ induced by $sk$ which factor through the first projection of the fibre product of $\psi$ with the unit section of $E.L$ over $\operatorname{Spec} k$, and $e$ is additive: $e(x+y) = E'.L$-sum of $e(x)$ and $e(y)$ for all $x,y$.
--
--   The set cut out by factorisation through the first projection of the pullback of $\psi$ along the unit section is the scheme-theoretic kernel of $\psi$, so the assertion is that the geometric points of $\ker \psi$ form a group isomorphic to $(\mathbb{Z}/\ell)^2$ — the classical statement that the isogeny dual to an $\ell$-level isogeny of fake elliptic curves again has kernel of type $(\mathbb{Z}/\ell)^2$. It supplies the geometric input for constructing an extra level structure at $\ell$ on the target curve, and is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flip_of_not_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flip_of_not_dvd) and [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_symm_of_not_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_symm_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_kernel_dual_of_not_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (hℓN : ¬ ℓ ∣ N)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) (E' : FakeEllipticCurve Λ N k)
    (φ : u.1.A ⟶ E'.A) (hφ : φ ≫ E'.f = u.1.f) (ψ : E'.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = E'.f)
    (φ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ E'.act x) (ψ_act : ∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ u.1.act x)
    (hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t ℓ Q)
    (hkerφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = E'.L.one t ↔ FactorsThrough u.2.levK P)
    (φ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough E'.lev (mapPt φ hφ P)) :
    ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), (ℓ : k') ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k' sk) E'.f //
          FactorsThrough (CategoryTheory.Limits.pullback.fst ψ (u.1.L.one (𝟙 (Spec (CommRingCat.of k)))).1) P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k' sk) E'.f) =
          E'.L.mul (geomPoint k' sk) (e x) (e y) := by sorry
