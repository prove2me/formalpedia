-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/60c8f84d-0dc8-5611-82dd-468a4c8c87b5
-- title:
--   Translate relation from a σ-level series identity
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, and an $\mathcal O$-algebra $O_{nr}$. Let $\Phi$ be a formal $\mathcal O_D$-module of height data `FormalODModule r` over $O_{nr}/(r)$, let $X_0$ be such a module over $O_{nr}/(\pi)$, and let $\kappa : O_{nr}/(\pi) \to O_{nr}/(r)$ be a ring homomorphism. Let $\beta_0$ be a homomorphism of formal $\mathcal O_D$-modules $\Phi \to \kappa_*X_0$ and $\beta_0'$ one in the other direction, with $\beta_0 \circ \beta_0' = [r^N]$ on $\kappa_*X_0$ (the action of $(r)^N$ in $\mathbb Z_{r^2}$). Let $B$ be an $\mathcal O$-algebra, $\psi : O_{nr} \to B$ an $\mathcal O$-algebra map, $\chi : O_{nr} \to B$ a ring map, $X$ a formal $\mathcal O_D$-module over $B$, and $t,t'$ rigidified objects of `Rigidified r Φ B` with $t.X = t'.X = X$. Let $\kappa_B : B/(\pi) \to B/(r)$ satisfy $\kappa_B \circ (\bmod \pi) = (\bmod r)$ and $\kappa_B \circ \overline{\psi} = \psi_* \circ \kappa$, where $\overline\psi$ is the induced map of $\pi$-quotients and $\psi_*$ that of $r$-quotients. Let $\sigma,\sigma'$ be two-variable series over $B/(\pi)$ with vanishing constant coefficients, and $j,j'$ natural numbers, such that $t.\rho = (\kappa_B)_*\sigma \circ \psi_*\beta_0 \circ \mathrm{Frob}^j$ and $t'.\rho = (\kappa_B)_*\sigma' \circ \psi_*\beta_0 \circ \mathrm{Frob}^{j'}$, where $\mathrm{Frob}^j$ is the series $X_i \mapsto X_i^{r^j}$. Assume $\sigma$ intertwines the $r^N$-multiplication series of $X.F$ reduced mod $\pi$ with that of $X_0.F$ pushed along the residue map $\overline\psi$, and that for a series $\varepsilon'$ over $O_{nr}/(\pi)$ with vanishing constant coefficients and natural numbers $a,c$ one has $[r^a]\circ\sigma' = [r^c]\circ(\sigma\circ\overline\psi_*\varepsilon')$, all multiplication series taken in $X.F$ mod $\pi$. Put $e' = \beta_0' \circ \kappa_*\varepsilon' \circ \beta_0$, and assume the Frobenius commutation $\mathrm{Frob}^j \circ \chi_*e' = \psi_*e' \circ \mathrm{Frob}^j$. Finally let $k,m'$ be natural numbers with $t.n + k + c = t'.n + N + a$ and $j' + m' = j + 2k$. Then `Rigidified.IsTranslate e' k m' χ t t'` holds: $t'.X = t.X$ and there is a natural number $c_0$ with $[r^{c_0+t.n+k}] \circ t'.\rho \circ \mathrm{Frob}^{m'} = [r^{c_0+t'.n}] \circ t.\rho \circ \chi_*e' \circ \mathrm{Frob}^{2k}$, the multiplications by powers of $r$ being taken in $X$ reduced modulo $r$.
--
--   This is the linking step in the Cherednik–Drinfeld uniformisation chain which converts an identity between the $\sigma$-level series attached to two rigidifications into the translate relation between the associated rigidified special formal modules. It is used in the comparison of rigidifications of fake elliptic curves, in particular in the transport lemmas for rigidifications and in the statement about the Atkin–Lehner action on $G$-points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)) (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (χ : Onr →+* B)
    (X : FormalODModule r B) (t t' : Rigidified r Φ B) (hXt : t.X = X) (hXt' : t'.X = X)

    (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
    (hκB₁ : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B))
    (hκB₂ : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ)
    (σ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (j j' : ℕ)
    (ht : t.ρ = (Series.map κB σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp (frobSeries (p := r) _ j)))
    (ht' : t'.ρ = (Series.map κB σ').comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp (frobSeries (p := r) _ j')))

    (hσN : (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ N))).comp σ =
      σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries (r ^ N))))

    (ε' : Series (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hε'0 : ∀ i, MvPowerSeries.constantCoeff (ε' i) = 0) (a c : ℕ)
    (hσσ' : (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ a))).comp σ' =
      (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries (r ^ c))).comp
        (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε')))

    (e' : Series (Onr ⧸ pIdeal r Onr)) (he' : e' = β₀'.comp ((Series.map κ ε').comp β₀))
    (hfrob : (frobSeries (p := r) _ j).comp (Series.map (residueMap χ) e') =
      (Series.map (residueMap (ψ : Onr →+* B)) e').comp (frobSeries (p := r) _ j))

    (k m' : ℕ) (hk : t.n + k + c = t'.n + N + a) (hm : j' + m' = j + 2 * k) :
    Rigidified.IsTranslate e' k m' χ t t' := by sorry
