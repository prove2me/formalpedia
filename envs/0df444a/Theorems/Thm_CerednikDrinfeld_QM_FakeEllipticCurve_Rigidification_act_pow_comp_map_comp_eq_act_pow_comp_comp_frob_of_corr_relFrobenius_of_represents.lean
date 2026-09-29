-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0687dd1d-f16b-5f3f-80bc-57eb081dd01f
-- title:
--   Relative Frobenius correspondence of rigidifications in formal coordinates
-- statement:
--   Fix a prime $r$ and a level $N$, a commutative ring $\mathcal O$ with an element $\pi$ generating the same ideal as $r$, an $\mathcal O$-algebra $O^{\mathrm{nr}}$ and an $\mathcal O$-algebra automorphism $\mathrm{Fr}$ of $O^{\mathrm{nr}}$ with $\mathrm{Fr}(x)-x^{r}\in\pi O^{\mathrm{nr}}$ for all $x$; write $k_0=O^{\mathrm{nr}}/\pi$. Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing every integer, and an order coordinate map $\mathrm{coord}\colon\Lambda\to \mathrm{W}(\mathbb F_{r^{2}})^{2}$ (additive, sending $1$ to $(1,0)$, multiplicative in the Frobenius-twisted sense, injective, with dense image modulo all powers of $r$, and matching reduced traces). Over $k_0$ are given a fake elliptic curve $A_0$ with $\Lambda$-action and level $N$, a formal $\mathcal O_D$-module $X_0$ of two variables over $k_0$ and formal coordinates $\theta_0$ for $A_0$ exhibiting $A_0$ as a formal module via $\mathrm{coord}$ and $X_0$; a second fake elliptic curve $A_0^{(r)}$ over $k_0$ together with $\mathrm{pr}\colon A_0^{(r)}\to A_0$ exhibiting $A_0^{(r)}$ as the pullback of $A_0$ along the map $k_0\to k_0$ induced by $\mathrm{Fr}$ (Cartesian square, compatible with group laws, $\Lambda$-actions and level structures); and a $k_0$-morphism $F\colon A_0\to A_0^{(r)}$ commuting with the $\Lambda$-actions such that for every commutative ring $C$ of characteristic $r$ and every point $x\colon \operatorname{Spec}C\to A_0$ one has $x$ followed by $F$ followed by $\mathrm{pr}$ equal to $\operatorname{Spec}$ of the Frobenius of $C$ followed by $x$. Over an $\mathcal O$-algebra $L$ are given $\mathcal O$-algebra maps $\psi,\psi'\colon O^{\mathrm{nr}}\to L$ with $\psi'=\psi\circ\mathrm{Fr}$, fake elliptic curves $E,E'$ over $L$, and a morphism $q\colon E\to E'$ over $L$ compatible with the group laws and with the $\Lambda$-actions; further a rigidification $\rho$ of $E$ relative to $(r,\pi,A_0,\psi)$ and a rigidification $\rho'$ of $E'$ relative to $\psi'$, each consisting of reductions $E_b,A_b$ over $L/\pi$ with comparison maps $g_b,g_A$ to $E$ resp. $A_0$, an exponent $d$ and an isogeny pair $\varphi,\varphi'$ of degree $r^{d}$ between $E_b$ and $A_b$ preserving the level. These are linked by: $q_b\colon \rho.E_b\to\rho'.E_b$ over $L/\pi$ with $q_b$ followed by $\rho'.g_b$ equal to $\rho.g_b$ followed by $q$; $u_A$ exhibiting $\rho'.A_b$ as the pullback of $A_0^{(r)}$ along the reduction of $\psi$, with $u_A$ followed by $\mathrm{pr}$ equal to $\rho'.g_A$; $F_b\colon\rho.A_b\to\rho'.A_b$ over $L/\pi$ with $F_b$ followed by $u_A$ equal to $\rho.g_A$ followed by $F$; and, for natural numbers $i,j$, the correspondence identity $q_b\gg\rho'.\varphi\gg[r^{i}]=\rho.\varphi\gg F_b\gg[r^{j}]$, where $[n]$ is the action of $n\in\Lambda$ on $\rho'.A_b$. Finally, formal coordinates $\theta,\theta'$ exhibit $E,E'$ as formal modules via $\mathrm{coord}$ and two-variable formal $\mathcal O_D$-modules $X,X'$ over $L$; pairs of power series $\sigma,\sigma'$ over $L/\pi$ with zero constant terms represent $\rho.\varphi'$ followed by $\rho.g_b$, resp. $\rho'.\varphi'$ followed by $\rho'.g_b$, in the coordinates $\theta_0$ on the source and $\theta$ resp. $\theta'$ on the target, for all test algebras that are simultaneously algebras over $L/\pi$, over $L$ and over $k_0$ compatibly with the quotient map and with the reduction of $\psi$ resp. $\psi'$, and all nilpotent-ideal parameters; and a pair of power series $\hat q$ over $L$ with zero constant terms represents $q$, in the sense that for every $L$-algebra $B$, every ideal $J$ with $J^{n+1}=0$ and every $s\in J^{2}$ one has $\theta(s)$ followed by $q$ equal to $\theta'$ evaluated at the truncated values of $\hat q$ at $s$. The conclusion is the identity of pairs of power series over $L/\pi$ $$[r^{\rho'.d+i}]\circ\big(\bar{\hat q}\circ\sigma\big)=[r^{\rho.d+j}]\circ\big(\sigma'\circ(X_1^{r},X_2^{r})\big),$$ where $\bar{\hat q}$ is the reduction of $\hat q$ modulo $\pi$ and $[r^{m}]$ denotes the action of $r^{m}\in \mathrm{W}(\mathbb F_{r^{2}})$ on the reduction of $X'$ modulo $\pi$.
--
--   This is the power-series incarnation, on the formal groups along the unit sections, of a relative-Frobenius correspondence between the rigidification of a fake elliptic curve and that of its twist by the unramified Frobenius, as used in the Čerednik–Drinfeld description of the rigid uniformisation. It feeds the statement [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isPiTranslate_of_isRigTransport_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isPiTranslate_of_isRigTransport_of_corr_relFrobenius_of_isAtkinLehnerQuotientVia), where the displayed identity is converted into the assertion that the correspondence acts as translation by $\pi$ on the rigidifying data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f)
    (hFlin : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x)
    (hFfrob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
        x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)

    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψ ψ' : Onr →ₐ[𝒪] L) (hψ' : ψ' = ψ.comp (Fr : Onr →ₐ[𝒪] Onr))
    (E E' : FakeEllipticCurve Λ N L) (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t E.f),
      mapPt q hq (E.L.mul t P Q) = E'.L.mul t (mapPt q hq P) (mapPt q hq Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ q = q ≫ E'.act x)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ' E')
    (qb : ρ.Eb.A ⟶ ρ'.Eb.A) (hqb : qb ≫ ρ'.gb = ρ.gb ≫ q) (hqbf : qb ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ A₀r.A)
    (huA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρ'.Ab uA)
    (huAg : uA ≫ prA = ρ'.gA)
    (Fb : ρ.Ab.A ⟶ ρ'.Ab.A) (hFb : Fb ≫ uA = ρ.gA ≫ F) (hFbf : Fb ≫ ρ'.Ab.f = ρ.Ab.f)
    (i j : ℕ)
    (hcorr : qb ≫ ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρ'.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ')
    (σ : Series (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B''] [Algebra L B'']
            [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
            algebraMap L B'' = (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (Ideal.Quotient.mk _) →
            algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
              (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
            ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
              ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
                PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'')) →
                PA ≫ ρ.gA = (θ₀ B'' s).1 →
                  PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (σ' : Series (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B''] [Algebra L B'']
            [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
            algebraMap L B'' = (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (Ideal.Quotient.mk _) →
            algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
              (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ') →
            ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
              ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ'.Ab.A,
                PA ≫ ρ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'')) →
                PA ≫ ρ'.gA = (θ₀ B'' s).1 →
                  PA ≫ ρ'.φ' ≫ ρ'.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))
    (qhat : Series L) (hq0 : ∀ i, MvPowerSeries.constantCoeff (qhat i) = 0)
    (hrep : ∀ (B'' : Type) [CommRing B''] [Algebra L B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ q = (θ' B'' (fun i => MvFormalGroup.nilEval n (qhat i) s)).1) :
    ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i))).comp
        ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) qhat).comp σ) =
      ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ.d + j))).comp
        (σ'.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (L ⧸ Ideal.span {algebraMap 𝒪 L π})) ^ r) := by sorry
