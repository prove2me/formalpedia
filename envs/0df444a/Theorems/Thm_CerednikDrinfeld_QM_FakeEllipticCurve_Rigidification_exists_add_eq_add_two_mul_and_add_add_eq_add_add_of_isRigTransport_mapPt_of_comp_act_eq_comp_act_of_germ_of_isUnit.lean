-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/09116189-f4b0-52f7-9e2e-3ba443ded76d
-- title:
--   Exponent bookkeeping for two rigidification transports linked by an isogeny
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $Onr$ with an $\mathcal O$-algebra automorphism $Fr$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing all rational integers, a level $N$, and a coordinate map $\mathrm{coord}:\Lambda\to \mathbb Z_{r^2}^2$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted product, injective, with dense image and the prescribed trace identity). Over $Onr/(\pi)$ one is given a fake elliptic curve $A_0$, a formal $\mathcal O_D$-module $X_0$ and formal coordinates $\theta_0$ of dimension $2$ exhibiting $A_0$ as a formal module via $\mathrm{coord}$; further $\iota:\mathbb Z_{r^2}\to Onr$, a formal $\mathcal O_D$-module $\Phi$ over $Onr/(r)$, a ring map $\kappa:Onr/(\pi)\to Onr/(r)$, and series $\beta_0,\beta_0'$ over $Onr/(r)$ which are $\mathcal O_D$-module homomorphisms $\Phi\to X_0\otimes_\kappa$ and back, with $\beta_0\circ\beta_0'=[r^{N_0}]$. Over a nonzero Noetherian $\mathcal O$-algebra $B$ with $(\pi)=(r)$ and $\pi$ nilpotent, with leg $\psi:Onr\to B$: fake elliptic curves $E,E_f$, a formal $\mathcal O_D$-module $X$ over $B$ and coordinates $\theta$ exhibiting $E$ as a formal module via $\mathrm{coord}$, a morphism $q:E.A\to E_f.A$ over $B$ such that the pushed-forward coordinates $q\circ\theta$ exhibit $E_f$ as a formal module via the same $X$, rigidifications $\rho$ of $E$ and $\rho_f$ of $E_f$ relative to $A_0$, and rigidified objects $t,t'$ (each consisting of a formal $\mathcal O_D$-module, a natural number and a series over $B/(r)$) with $t.X=t'.X=X$, which are `IsRigTransport`s of $\theta_0,\kappa,\beta_0$ along $\rho$ with $\theta$ at level $j\le 1$, respectively along $\rho_f$ with $q\circ\theta$ at level $j'\le 1$, and which are admissible for $\iota$ and the Frobenius twists $\psi\circ Fr^{-j}$, $\psi\circ Fr^{-j'}$ (special, of height $4$, with $\rho$-series an isogeny of height $4n$). Finally: $q_b$ on the reductions with $q_b$ followed by $\rho_f.g_b$ equal to $\rho.g_b$ followed by $q$; $u_A:\rho_f.A_b.A\to\rho.A_b.A$ exhibiting $\rho_f.A_b$ as pullback of $\rho.A_b$ along the identity and compatible with $\rho.g_A,\rho_f.g_A$; an endomorphism $f'$ of $A_0$ over $A_0.f$ with a lift $f'_b$ on $\rho.A_b$; natural numbers $n=u\,r^\alpha$ and $n'=u\,v\,r^\beta$ with $u,v$ units in $\mathbb Z_{r^2}$, satisfying the correspondence identity $u_A\,f'_b\,\rho.\varphi'\,q_b$ followed by translation by $n$ on $\rho_f.E_b$ equals $\rho_f.\varphi'$ followed by translation by $n'$; an endomorphism $\varepsilon'$ of the formal group $X_0.F$ which is the germ of $f'$, in the sense that for every $Onr/(\pi)$-algebra $B'$, ideal $J$ with $J^{m+1}=0$ and $s$ with entries in $J$ one has $\theta_0(\varepsilon'(s))=f'\circ\theta_0(s)$; the series $e''=\beta_0'\circ\kappa\bigl(\varepsilon'\circ[v^{-1}]\bigr)\circ\beta_0$; and the hypothesis that the base change of $e''$ to $B/(r)$ along the residue map of $\psi$ has kernel of degree $r^{2m'}$ (kernel algebra finite and projective, of rank $r^{2m'}$ after any base change to a field). The conclusion is that there is a natural number $k$ with $j'+m'=j+2k$ and $t.n+k+\alpha=t'.n+N_0+\beta$.
--
--   This is the numerical bookkeeping step of the Čerednik–Drinfeld dictionary in the case where the two rigidified objects sit on curves joined by an isogeny $q$ of degree prime to $r$: the parity datum $j$, the height $m'$ of the transported germ, the rigidification levels $t.n$, $t'.n$, the exponent $N_0$ and the exponents $\alpha,\beta$ of the correspondence are tied together by two linear relations. It is used in the construction of the quaternionic action on rigidified points, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪)
    {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N₀ : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N₀))

    {B : Type} [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hπB : Ideal.span {algebraMap 𝒪 B π} = pIdeal r B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (E Ef : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f)
    (hEf : Ef.IsFormalModuleVia coord X (fun B' _ _ s => mapPt q hq (θ B' s)))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef)

    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X)
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρf (fun B' _ _ s => mapPt q hq (θ B' s)) j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (qb : ρ.Eb.A ⟶ ρf.Eb.A) (hqb : qb ≫ ρf.gb = ρ.gb ≫ q)
    (uA : ρf.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (huAg : uA ≫ ρ.gA = ρf.gA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (n n' : ℕ)
    (hcurve : uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρf.φ' ≫ ρf.Eb.act ⟨(((n' : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (u v α β : ℕ) (hn : n = u * r ^ α) (hn' : n' = u * v * r ^ β)
    (hu : IsUnit ((u : ℕ) : Zp2 r)) (hv : IsUnit ((v : ℕ) : Zp2 r))

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s))
    (e'' : Series (Onr ⧸ pIdeal r Onr))
    (he'' : e'' = β₀'.comp ((Series.map κ (Series.comp ε'.toPowerSeries (X₀.act ((hv.unit⁻¹ : (Zp2 r)ˣ) : Zp2 r)))).comp β₀))

    (m' : ℕ) (hker : FormalODModule.HasKernelOfDegree (Series.map (residueMap (ψ : Onr →+* B)) e'') (r ^ (2 * m'))) :
    ∃ k : ℕ, j' + m' = j + 2 * k ∧ t.n + k + α = t'.n + N₀ + β := by sorry
