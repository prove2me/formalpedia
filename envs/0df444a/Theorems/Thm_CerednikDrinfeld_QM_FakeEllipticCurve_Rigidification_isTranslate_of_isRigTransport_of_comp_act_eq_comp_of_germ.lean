-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/3483a31d-a9d7-5794-8c61-96248353d8dd
-- title:
--   Transports of comparable rigidifications are translates
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{\mathrm{nr}}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ containing every rational integer, a level $N$, and a map $\mathrm{coord}\colon \Lambda \to \mathbb Z_{r^2}^{\,2}$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the twisted rule, injective, with dense image, and compatible with traces), where $\mathbb Z_{r^2} = W(\mathbb F_{r^2})$. Over $O^{\mathrm{nr}}/(\pi)$ let $A_0$ be a fake elliptic curve, $X_0$ a formal $\mathcal O_D$-module of dimension $2$, and $\theta_0$ formal coordinates for $A_0.f$ exhibiting $A_0$ as a formal module via $\mathrm{coord}$ and $X_0$. Let $\iota\colon \mathbb Z_{r^2}\to O^{\mathrm{nr}}$ be a ring map, $\Phi$ a formal $\mathcal O_D$-module over $O^{\mathrm{nr}}/(r)$, $\kappa\colon O^{\mathrm{nr}}/(\pi)\to O^{\mathrm{nr}}/(r)$ a ring map, and $\beta_0,\beta_0'$ two-variable series over $O^{\mathrm{nr}}/(r)$ which are $\mathcal O_D$-homomorphisms $\Phi \to \kappa_*X_0$ and $\kappa_*X_0 \to \Phi$ with $\beta_0\circ\beta_0' = [r^{N_0}]$ on $\kappa_*X_0$. Let $B$ be an $\mathcal O$-algebra with structural map $\psi\colon O^{\mathrm{nr}}\to B$, assume $\pi B = rB$, let $E$ be a fake elliptic curve over $B$ with formal $\mathcal O_D$-module $X$ and coordinates $\theta$ realising it as a formal module via $\mathrm{coord}$, and let $\rho,\rho'$ be two rigidifications of $E$ over $A_0$ and $\psi$. Let $j,j' \le 1$ and let $t,t'$ be rigidified objects for $\Phi$ over $B$ with $t.X = t'.X = X$, each a rigidification transport (`IsRigTransport`) of $\rho$, resp.\ $\rho'$, relative to $\theta_0$, $\kappa$, $\beta_0$, $\theta$ with parity $j$, resp.\ $j'$, and each admissible for $\iota$ and the leg $\psi\circ\mathrm{Fr}^{-j}$, resp.\ $\psi\circ\mathrm{Fr}^{-j'}$. Let $(u,uA)$ be a comparison of $\rho'$ with $\rho$ (pullbacks along the identity compatible with the maps $g_b$ and $g_A$), let $f'$ be an endomorphism of $A_0.A$ over the base and $f'_b$ an endomorphism of $\rho.A_b.A$ over its base with $f'_b$ followed by $\rho.g_A$ equal to $\rho.g_A$ followed by $f'$, and assume the curve-level identity that $\rho'.\varphi'$, $u$ and $\rho.E_b$-multiplication by $r^{e_a}$ compose to the same map as $uA$, $f'_b$, $\rho.\varphi'$ and $\rho.E_b$-multiplication by $r^{e_c}$. Let $\varepsilon'$ be an endomorphism of the formal group $X_0.F$ which is the germ of $f'$ in the coordinates $\theta_0$, i.e. for every $O^{\mathrm{nr}}/(\pi)$-algebra $B'$, ideal $J$ with $J^{m+1}=0$ and $s\colon \mathrm{Fin}\,2 \to J$ one has $\theta_0(B')$ applied to the truncated evaluations of $\varepsilon'$ at $s$ equal to $f'$ composed with $\theta_0(B')(s)$, and put $e' = \beta_0'\circ(\kappa_*\varepsilon')\circ\beta_0$. Assume the leg congruence that for all $x \in O^{\mathrm{nr}}/(r)$ the image of $x$ under the reduction of $\psi$ is the $r^j$-th power of its image under the reduction of $\psi\circ\mathrm{Fr}^{-j}$, and let $k,m'$ satisfy $t.n + k + e_c = t'.n + N_0 + e_a$ and $j' + m' = j + 2k$. Then $t'$ is the $(e',k,m')$-translate of $t$ for the leg $\psi\circ\mathrm{Fr}^{-j}$: $t'.X = t.X$ and there is $c$ with $[r^{c+t.n+k}]\circ t'.\rho\circ \mathrm{Frob}^{m'} = [r^{c+t'.n}]\circ t.\rho\circ (e'$ pushed along the reduction of $\psi\circ\mathrm{Fr}^{-j})\circ \mathrm{Frob}^{2k}$, the multiplications being taken in $t.\bar X$ and $\mathrm{Frob}^{n}$ denoting the substitution $X_i \mapsto X_i^{r^n}$.
--
--   This is the per-piece translation step in the Čerednik–Drinfeld comparison between rigidifications of a fake elliptic curve and rigidified formal $\mathcal O_D$-modules: an endomorphism of the base point $A_0$ relating two rigidifications of the same curve is converted, via its formal germ, into the explicit translate relation between their Drinfeld transports. It is used in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_isActBy_rigidifiedToG_star_of_isTranslateBy_of_isLevelIsogeny_of_isAtkinLehnerQuotient_of_endIsoFull), where the group action on the rigidified moduli functor is identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ
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
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X)
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ' θ j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (hcmp : FakeEllipticCurve.Rigidification.IsComparison ρ ρ' u uA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (ea ec : ℕ)
    (hcurve : ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ ea : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ ec : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s))
    (e' : Series (Onr ⧸ pIdeal r Onr)) (he' : e' = β₀'.comp ((Series.map κ ε'.toPowerSeries).comp β₀))

    (hχ : ∀ x : Onr ⧸ pIdeal r Onr,
      residueMap (ψ : Onr →+* B) x = (residueMap ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) x) ^ (r ^ j))

    (k m' : ℕ) (hk : t.n + k + ec = t'.n + N₀ + ea) (hm : j' + m' = j + 2 * k) :
    Rigidified.IsTranslate e' k m' ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) t t' := by sorry
