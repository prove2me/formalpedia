-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/4d817220-f33d-558e-a383-07db8c680727
-- title:
--   Re-basing a rigidification along a twisted coefficient leg
-- statement:
--   Fix a prime $r$ and a level $N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$ with an $\mathcal O$-algebra endomorphism $\sigma$, rationals $a,b$ and a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ containing every integer. Over the residue ring $k_0 := O^{nr}/(\pi)$ one is given two fake elliptic curves $A_0$, $A_0^{\sigma}$ for $(\Lambda,N)$ and a morphism $\mathrm{pr} : A_0^{\sigma} \to A_0$ exhibiting $A_0^{\sigma}$ as the pull-back of $A_0$ along the map $k_0 \to k_0$ induced by $\sigma$ (a pull-back square of schemes, compatibility with the relative group laws on $T$-points, intertwining of the $\Lambda$-actions, and preservation of points factoring through the level structure). One is further given morphisms $F : A_0 \to A_0^{\sigma}$ and $V : A_0^{\sigma} \to A_0$ over $k_0$ which are additive on $T$-points, commute with the $\Lambda$-actions ($\mathrm{act}(x)\,F = F\,\mathrm{act}(x)$ and likewise for $V$), with $F$ carrying points factoring through the level structure of $A_0$ to such points of $A_0^{\sigma}$, and satisfying $V \circ F = [r]$ on $A_0$-points and $F \circ V = [r]$ on $A_0^{\sigma}$-points. The conclusion: for every $\mathcal O$-algebra $B$, every $\mathcal O$-algebra map $\psi : O^{nr} \to B$, every fake elliptic curve $E$ over $B$ and every rigidification $\rho$ of $E$ relative to $A_0$ and the leg $\psi$ (consisting of $E_b, A_b$ over $B/(\pi)$ with their pull-back comparisons $g_b$ to $E$ and $g_A$ to $A_0$, an integer $d$, and an $r^d$-isogeny pair $\varphi, \varphi'$ respecting levels), there exist a rigidification $\rho^{+}$ of the same $E$ relative to the twisted leg $\psi \circ \sigma$, a morphism $u_b : \rho.E_b \to \rho^{+}.E_b$ over $B/(\pi)$ with $u_b$ followed by $\rho^{+}.g_b$ equal to $\rho.g_b$, a morphism $g_A' : \rho^{+}.A_b \to A_0^{\sigma}$ exhibiting $\rho^{+}.A_b$ as the pull-back of $A_0^{\sigma}$ along the map induced by $\psi$ and with $g_A'$ followed by $\mathrm{pr}$ equal to $\rho^{+}.g_A$, and morphisms $F_b : \rho.A_b \to \rho^{+}.A_b$ and $V_b : \rho^{+}.A_b \to \rho.A_b$ over $B/(\pi)$ with $F_b$ followed by $g_A'$ equal to $\rho.g_A$ followed by $F$ and $V_b$ followed by $\rho.g_A$ equal to $g_A'$ followed by $V$, such that $\rho^{+}.d = \rho.d + 1$, $u_b$ followed by $\rho^{+}.\varphi$ equals $\rho.\varphi$ followed by $F_b$, and $\rho^{+}.\varphi' = u_b \circ \rho.\varphi' \circ V_b$.
--
--   This is the re-basing step for rigidification data: a rigidification of $E$ along a coefficient leg $\psi$ is transported to the leg $\psi \circ \sigma$ at the cost of raising the isogeny height $d$ by one, using only the pull-back square for $\mathrm{pr}$ and the relations $VF = [r]$, $FV = [r]$ — in the applications $\sigma$ is a power of Frobenius and $(A_0^{\sigma}, F, V)$ is the Frobenius twist of the base point with its relative Frobenius and Verschiebung. It is used in the construction of Frobenius twists of rigidified objects and in the comparison of such twists with the relative Frobenius on the Čerednik–Drinfeld side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (σ : Onr →ₐ[𝒪] Onr)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π σ) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (F_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
      mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q))
    (V_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
      mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q))
    (F_act : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) (V_act : ∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x)
    (F_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P))
    (V_F : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P)
    (F_V : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
      ∃ (ρp : FakeEllipticCurve.Rigidification r π A₀ (ψ.comp σ) E)
        (ub : ρ.Eb.A ⟶ ρp.Eb.A) (_ : ub ≫ ρp.gb = ρ.gb) (_ : ub ≫ ρp.Eb.f = ρ.Eb.f)
        (gA' : ρp.Ab.A ⟶ A₀r.A) (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
        (_ : gA' ≫ prA = ρp.gA)
        (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (_ : Fb ≫ gA' = ρ.gA ≫ F) (_ : Fb ≫ ρp.Ab.f = ρ.Ab.f)
        (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (_ : Vb ≫ ρ.gA = gA' ≫ V) (_ : Vb ≫ ρ.Ab.f = ρp.Ab.f),
        ρp.d = ρ.d + 1 ∧ ub ≫ ρp.φ = ρ.φ ≫ Fb ∧ ρp.φ' = Vb ≫ ρ.φ' ≫ ub := by sorry
