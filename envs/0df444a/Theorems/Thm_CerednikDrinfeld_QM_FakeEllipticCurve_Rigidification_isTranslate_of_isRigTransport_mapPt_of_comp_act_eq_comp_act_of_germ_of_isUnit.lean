-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/3ebd7d3f-0b06-5956-9e7b-4b7b2882ae83
-- title:
--   Translate relation between transported rigidifications along an isogeny
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $Onr$ with an $\mathcal O$-algebra automorphism $Fr$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing every rational integer, and a level $N$. Data over the residue side: a map $\mathrm{coord}\colon\Lambda\to\mathbb Z_{r^2}\times\mathbb Z_{r^2}$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative in the Frobenius-twisted sense, injective, with dense image modulo all powers of $r$, and computing reduced traces), a fake elliptic curve $A_0$ over $Onr/(\pi)$, a formal $\mathcal O_D$-module $X_0$ over $Onr/(\pi)$, two-dimensional formal coordinates $\theta_0$ on $A_0.f$ with `A₀.IsFormalModuleVia coord X₀ θ₀`, a ring map $\iota\colon\mathbb Z_{r^2}\to Onr$, a formal $\mathcal O_D$-module $\Phi$ over $Onr/(r)$, a ring map $\kappa\colon Onr/(\pi)\to Onr/(r)$, series $\beta_0,\beta_0'$ over $Onr/(r)$ that are $\mathcal O_D$-homomorphisms $\Phi\to\kappa_*X_0$ and $\kappa_*X_0\to\Phi$ with $\beta_0\circ\beta_0'=[r^{N_0}]_{\kappa_*X_0}$. Over an $\mathcal O$-algebra $B$ with an $\mathcal O$-algebra map $\psi\colon Onr\to B$ and $(\pi)=(r)$ in $B$: fake elliptic curves $E,E_f$, a formal $\mathcal O_D$-module $X$, coordinates $\theta$ with `E.IsFormalModuleVia coord X θ`, a $B$-morphism $q\colon E.A\to E_f.A$ over the structural maps such that $E_f$ is a formal module via $\mathrm{coord}$, the same $X$ and the coordinates $\theta$ pushed forward by $q$, and rigidifications $\rho$ of $E$, $\rho_f$ of $E_f$ along $A_0$ and $\psi$. Further, $j\le 1$ and a rigidified object $t$ over $B$ with $t.X=X$, which is a rigidification transport of $\rho$ in $\theta$ at level $j$ (`IsRigTransport θ₀ κ β₀ ρ θ j t`) and is admissible for $\iota$ and the twisted leg $\psi\circ Fr^{-j}$; likewise $j'\le 1$ and $t'$ with $t'.X=X$, a transport of $\rho_f$ in the pushed coordinates at level $j'$, admissible for $\psi\circ Fr^{-j'}$. The geometric compatibilities are: $q_b\colon\rho.E_b.A\to\rho_f.E_b.A$ with $q_b$ followed by $\rho_f.g_b$ equal to $\rho.g_b$ followed by $q$; $u_A\colon\rho_f.A_b.A\to\rho.A_b.A$ exhibiting $\rho_f.A_b$ as the pullback of $\rho.A_b$ along the identity ring map, with $u_A$ followed by $\rho.g_A$ equal to $\rho_f.g_A$; an endomorphism $f'$ of $A_0.A$ over $A_0.f$ together with an endomorphism $f'_b$ of $\rho.A_b.A$ over $\rho.A_b.f$ covering $f'$ through $\rho.g_A$; and natural numbers $n,n'$ with the correspondence identity $u_A\,;f'_b\,;\rho.\varphi'\,;q_b\,;\rho_f.E_b.\mathrm{act}(n)=\rho_f.\varphi'\,;\rho_f.E_b.\mathrm{act}(n')$, where $n=u\,r^{\alpha}$ and $n'=u\,v\,r^{\beta}$ with $u,v$ units in $\mathbb Z_{r^2}$. Finally, $\varepsilon'$ is an endomorphism of the formal group $X_0.F$ inducing $f'$ on $\theta_0$-coordinates (for every $Onr/(\pi)$-algebra $B'$, ideal $J$ with $J^{m+1}=0$ and $s$ with entries in $J$, $\theta_0$ of the truncated evaluation of $\varepsilon'$ at $s$ equals $f'$ applied to $\theta_0(s)$), $e''$ is the series $\beta_0'\circ\kappa_*\bigl(\varepsilon'\circ X_0.\mathrm{act}(v^{-1})\bigr)\circ\beta_0$, the residue maps of $\psi$ and of $\psi\circ Fr^{-j}$ on $Onr/(r)$ differ by raising to the power $r^{j}$, and $k,m'$ satisfy $t.n+k+\alpha=t'.n+N_0+\beta$ and $j'+m'=j+2k$. The conclusion is `Rigidified.IsTranslate e'' k m' (ψ∘Fr^{-j}) t t'`: namely $t'.X=t.X$ and there is $c$ with $[r^{c+t.n+k}]_{t.\mathrm{Xbar}}\circ t'.\rho\circ\mathrm{frobSeries}(m')=[r^{c+t'.n}]_{t.\mathrm{Xbar}}\circ t.\rho\circ(\mathrm{residueMap}(\psi\circ Fr^{-j}))_*e''\circ\mathrm{frobSeries}(2k)$, where $\mathrm{frobSeries}(m)$ raises each variable to the power $r^{m}$.
--
--   This is the series-level comparison underlying the Čerednik–Drinfeld description of the action of correspondences on rigidified points: an isogeny $q$ of degree prime to $r$, together with an endomorphism $f'$ of the reduction datum $A_0$, transports one admissible rigidification to a translate of the other, with the translation recorded by the bookkeeping integers $k$, $m'$ and the series $e''$. It feeds the statement that the rigidified $G$-point attached to a fake elliptic curve is acted on as prescribed by Hecke operators at an auxiliary prime and by the Atkin–Lehner involution at $r$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
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

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hπB : Ideal.span {algebraMap 𝒪 B π} = pIdeal r B)
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

    (hχ : ∀ x : Onr ⧸ pIdeal r Onr,
      residueMap (ψ : Onr →+* B) x = (residueMap ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) x) ^ (r ^ j))

    (k m' : ℕ) (hk : t.n + k + α = t'.n + N₀ + β) (hm : j' + m' = j + 2 * k) :
    Rigidified.IsTranslate e'' k m' ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) t t' := by sorry
