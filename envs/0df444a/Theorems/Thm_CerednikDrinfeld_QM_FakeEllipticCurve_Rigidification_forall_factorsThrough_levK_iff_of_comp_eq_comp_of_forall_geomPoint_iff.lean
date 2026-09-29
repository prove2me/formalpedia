-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/d65b1f5c-4365-5dc2-bed4-4b0f258992fc
-- title:
--   Prime-to-r extra levels agree for compatible rigidifications
-- statement:
--   Fix a prime $r$, an integer $N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $Onr$, rationals $a,b$, and a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing every integer. Let $A_0$ be a fake elliptic curve of level $N$ for $\Lambda$ over $Onr/(\pi)$, let $B$ be a Noetherian $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, let $\psi,\psi':Onr\to B$ be $\mathcal O$-algebra maps, let $E$ be a fake elliptic curve of level $N$ for $\Lambda$ over $B$, and let $\rho$, $\rho'$ be rigidifications of $E$ with respect to $r,\pi$ and to $\psi$, $\psi'$ respectively: each supplies a curve $E_b$ over $B/(\pi)$ with $g_b:E_b.A\to E.A$ exhibiting $E_b$ as the pullback of $E$, a curve $A_b$ over $B/(\pi)$ with $g_A:A_b.A\to A_0.A$ exhibiting $A_b$ as the pullback of $A_0$ along the map induced by $\psi$ (resp. $\psi'$), an exponent $d$, and a level-preserving isogeny pair $\varphi,\varphi'$ of degree $r^{\,d}$ between $E_b$ and $A_b$. Assume given $u_b:\rho.E_b.A\to\rho'.E_b.A$ with $u_b\circ$-composites satisfying $u_b\mathbin{;}\rho'.g_b=\rho.g_b$ and $u_b\mathbin{;}\rho'.E_b.f=\rho.E_b.f$, and an endomorphism $\theta$ of the scheme $A_0.A$ (not required to lie over $Onr/(\pi)$) with $u_b$ followed by $\rho'.\varphi$ followed by $\rho'.g_A$ equal to $\rho.\varphi$ followed by $\rho.g_A$ followed by $\theta$. Let $\ell\neq r$ be a prime whose image in $B$ is a unit, and let $K_0$ be an extra level at $\ell$ on $A_0$ (a closed immersion $K_0.K\to A_0.A$, finite, flat and of finite presentation of rank $\ell^2$ over the base, whose points form a $\Lambda$-stable subgroup killed by $\ell$, meeting the level-$N$ structure only in the unit, with geometric fibres $(\mathbb Z/\ell)^2$). Suppose $m$ is a natural number with $\ell\nmid m$ such that for every algebraically closed field $k$, every $t:\operatorname{Spec}k\to\operatorname{Spec}(Onr/(\pi))$ and every $x:\operatorname{Spec}k\to A_0.A$ over $t$, the composite $x$ followed by $\theta$ factors through $K_0.levK$ if and only if the $m$-fold sum $m\cdot x$ for the group law of $A_0$ does. Finally let $C,C'$ be extra levels at $\ell$ on $E$ such that for every scheme $T$, every $t':T\to\operatorname{Spec}(B/(\pi))$ and every $T$-point $R$ of $\rho.E_b$ over $t'$, if $R$ followed by $\rho.g_b$ factors through $C.levK$ then $R$ followed by $\rho.\varphi$ and $\rho.g_A$ factors through $K_0.levK$, and symmetrically for $\rho'$, $C'$. Then for every scheme $T$, every $t:T\to\operatorname{Spec}B$ and every $T$-point $R$ of $E$ over $t$, $R$ factors through $C.levK$ if and only if it factors through $C'.levK$.
--
--   This is the rigidity statement that the auxiliary $\ell$-level structure on a fake elliptic curve transported from the base point $A_0$ does not depend on the chosen rigidification: two rigidifications whose isogenies to $A_0$ differ by the transport map $\theta$, which acts on geometric $\ell$-level points of $A_0$ as multiplication by a prime-to-$\ell$ integer, cut out extra levels on $E$ with the same points on every base. It is used in the construction of rigidifications with prescribed Frobenius twist and compatible level structures in the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (ψ ψ' : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ' E)
    (ub : ρ.Eb.A ⟶ ρ'.Eb.A) (hub : ub ≫ ρ'.gb = ρ.gb) (hub' : ub ≫ ρ'.Eb.f = ρ.Eb.f)
    (θ : A₀.A ⟶ A₀.A) (hθ : ub ≫ ρ'.φ ≫ ρ'.gA = ρ.φ ≫ ρ.gA ≫ θ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓ : IsUnit ((ℓ : ℕ) : B))
    (K₀ : A₀.ExtraLevel ℓ) (m : ℕ) (hm : ¬ ℓ ∣ m)
    (hθK : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})))
        (x : SchemeHomOver t A₀.f),
        (∃ Q₀ : Spec (CommRingCat.of k) ⟶ K₀.K, Q₀ ≫ K₀.levK = x.1 ≫ θ) ↔
          (∃ Q₀ : Spec (CommRingCat.of k) ⟶ K₀.K, Q₀ ≫ K₀.levK = (nsmulPt A₀.L t m x).1))
    (C C' : E.ExtraLevel ℓ)
    (hC : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
      (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA))
    (hC' : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ'.Eb.f),
      (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ρ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ'.φ) ≫ ρ'.gA)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R := by sorry
