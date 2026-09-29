-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_nthSeries_eq_comp_comp_of_forall_nilEval_of_comp_act_comp_eq_of_constantCoeff_eq_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_nthSeries_eq_comp_comp_of_forall_nilEval_of_comp_act_comp_eq_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/cef1f644-9cc5-5188-8575-2ff97f5ee5c1
-- title:
--   Comparison of rigidifications: an identity of r-power series
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $Onr$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$ containing the image of every integer (hypothesis `hΛℤ`), a level $N$, and a map $coord : \Lambda \to \mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$ (Witt vectors of $\mathbb F_{r^2}$) satisfying `IsOrderCoord`: additive, sending $1$ to $(1,0)$, multiplicative in the twisted sense involving $r$ and the Witt Frobenius, injective, with dense image modulo every power of $r$, and with the trace compatibility $(coord\,m)_1+\varphi((coord\,m)_1)=n$ whenever $m+\bar m=n$. Over $k_0 = Onr/(\pi)$ take a fake elliptic curve $A_0$ for $(\Lambda,N)$, a formal $\mathcal O_D$-module $X_0$ of the `FormalODModule` kind for $r$, and two-dimensional formal coordinates $\theta_0$ for $A_0.f$; over an $\mathcal O$-algebra $B$ with leg $\psi : Onr \to B$ take a fake elliptic curve $E$, a formal module $X$ and coordinates $\theta$ with `E.IsFormalModuleVia coord X θ`, i.e. $\theta$ are formal coordinates for the group law of $E$ with formal group $X.F$, and the $\Lambda$-action is computed by the series $a\mapsto X.act$ added via $X.F$ to $X.act$ composed with $X.varpi$. Let $\rho,\rho'$ be rigidifications of $E$ over $A_0$ along $\psi$. Let $\sigma,\sigma'$ be pairs of two-variable power series over $B/(\pi)$ with vanishing constant coefficients which represent the quasi-inverse legs: for every ring $B''$ that is simultaneously a $B$-, $B/(\pi)$- and $k_0$-algebra, with $B\to B''$ factoring through $B/(\pi)$ and $k_0\to B''$ equal to the residue leg `residueLeg π ψ` followed by $B/(\pi)\to B''$, for every ideal $J$ with $J^{m+1}=0$, every $s : \mathrm{Fin}\,2 \to J$ and every $PA : \operatorname{Spec} B'' \to \rho.Ab.A$ lying over $\operatorname{Spec}(B/(\pi))$ with $\rho.gA\circ PA$ equal to the point $\theta_0(s)$, the composite of $PA$ with $\rho.\varphi'$ and $\rho.gb$ is the point $\theta$ evaluated at the truncated values $\mathrm{nilEval}\,m\,(\sigma_i)\,s$ (and likewise for $\rho',\sigma'$). Assume a comparison $(u,u_A)$ between $\rho$ and $\rho'$ (each of $u,u_A$ exhibiting the $\rho'$-object as a pullback of the $\rho$-object along the identity and commuting with $gb$, resp. $gA$), an endomorphism $f'$ of $A_0.A$ over $A_0.f$, an endomorphism $f'_b$ of $\rho.Ab.A$ over $\rho.Ab.f$ with $\rho.gA\circ f'_b = f'\circ \rho.gA$, natural numbers $e_a,e_c$ with the curve identity $[r^{e_a}]_{\rho.Eb}\circ u\circ \rho'.\varphi' = [r^{e_c}]_{\rho.Eb}\circ \rho.\varphi'\circ f'_b\circ u_A$ (the $\Lambda$-actions at the integers $r^{e_a},r^{e_c}$), and an endomorphism $\varepsilon'$ of the formal group $X_0.F$ which is the germ of $f'$ in $\theta_0$-coordinates, in the sense that $\theta_0$ applied to the truncations of $\varepsilon'$ at any nilpotent $s$ equals $f'$ applied to the point $\theta_0(s)$. Then, as pairs of power series over $B/(\pi)$, the reduction of $X.F.nthSeries(r^{e_a})$ composed with $\sigma'$ equals the reduction of $X.F.nthSeries(r^{e_c})$ composed with $\sigma$ composed with the image of $\varepsilon'$ under `residueLeg π ψ`.
--
--   This is the formal-module shadow of a comparison between two rigidifications in the Čerednik–Drinfeld uniformisation: an identity between quasi-inverse legs of rigidifications, twisted by powers of the $\Lambda$-action, is transported into an identity of two-variable power series over $B/(\pi)$ relating the $r^{e_a}$- and $r^{e_c}$-multiplication series of the formal module $X$. It is used by the lemmas that analyse translates of rigidifications and compare their rigidification exponents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_nthSeries_eq_comp_comp_of_forall_nilEval_of_comp_act_comp_eq_of_constantCoeff_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_nthSeries_eq_comp_comp_of_forall_nilEval_of_comp_act_comp_eq_of_constantCoeff_eq_zero
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (σ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ'.Ab.A,
            PA ≫ ρ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ'.gA = (θ₀ B'' s).1 →
              PA ≫ ρ'.φ' ≫ ρ'.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))

    (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (hcmp : FakeEllipticCurve.Rigidification.IsComparison ρ ρ' u uA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (ea ec : ℕ)
    (hcurve : ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ ea : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ ec : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s)) :
    (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ ea))).comp σ' =
      (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ ec))).comp
        (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries)) := by sorry
