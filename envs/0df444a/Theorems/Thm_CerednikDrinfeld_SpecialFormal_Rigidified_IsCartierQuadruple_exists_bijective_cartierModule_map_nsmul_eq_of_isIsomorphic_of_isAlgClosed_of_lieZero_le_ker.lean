-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/34dad902-fb40-50a8-b21c-ada01ddf6ca8
-- title:
--   Dieudonné-module isomorphism from isomorphic Cartier quadruples
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon W(\mathbf F_{p^2})\to W(k)$, and let $\Phi$ be a formal $\mathcal O_D$-module of dimension $2$ over $W(k)/pW(k)$ (a commutative two-variable formal group law with commuting actions of $W(\mathbf F_{p^2})$ and of a uniformiser $\varpi$ satisfying $\varpi^2=p$, $\varpi a=\sigma(a)\varpi$), with $j=\iota$ followed by reduction modulo $p$. Assume: $\Phi$ is special, i.e. $\mathrm{Lie}_0\Phi$ and $\mathrm{Lie}_1\Phi$ are complementary and both invertible; $\Phi$ has height $4$, i.e. the kernel of multiplication by $p$ has degree $p^4$; $\mathrm{Lie}_0\Phi\subseteq\ker\mathrm{Lie}(\varpi)$; the two graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ (those $f$ with $\langle\mathrm{teich}\,c\rangle_*f=j(\mathrm{teich}\,c)^{p^n}f$ for all $c\in\mathbf F_{p^2}$) are complementary; and an additive map $r_\Phi\colon\mathbf Z_p^2\to N(M_\Phi)$ for the associated graded Cartier module data is given which, for every canonical $L$-map $L$, maps all of $\mathbf Z_p^2$ bijectively onto the $\eta$-piece of degree $0$ attached to $L$. Let $\kappa$ be an algebraically closed field of characteristic $p$ which is a $\mathbf Z_p$-algebra, $\psi\colon W(k)\to\kappa$ a ring homomorphism, and let $t=(X,n,\rho)$ and $t'=(X',n',\rho')$ be rigidified data over $\kappa$ (a formal $\mathcal O_D$-module, a natural number, and a tuple of power series over $\kappa/p\kappa$) which are admissible: $X$ is special for the structure map induced by $\iota,\psi$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$, and likewise for $t'$. Let $Q,Q'$ be Drinfeld data over $\kappa$ for $K=\mathbf Q_p$ and the uniformiser $p\in\mathbf Z_p$, satisfying `IsCartierQuadruple` with respect to $t$ and $t'$ respectively (so in particular $\rho$, $\rho'$ are homomorphisms of formal $\mathcal O_D$-modules, the invertible modules $T_0,T_1$ of the datum are identified with $\mathrm{Lie}_0$, $\mathrm{Lie}_1$ of $X$ compatibly with $\Pi_0,\Pi_1$ and $\mathrm{Lie}(\varpi)$, and the lattices $N_0,N_1$ together with the maps $u_0,u_1$ are described by $\eta$-sections over affine opens), and assume $Q$ and $Q'$ are isomorphic. Then there exist a commutative two-variable formal group law $\Psi$ over $\kappa$, homomorphisms $\rho_\kappa\colon\Psi\to X$ and $\rho'_\kappa\colon\Psi\to X'$ whose power series reduce modulo $p\kappa$ to $\rho$ and $\rho'$, and an additive bijection $\theta$ from the Cartier module of $X$ to that of $X'$ commuting with Frobenius, with Verschiebung, with the homotheties $\langle a\rangle$ for $a\in\kappa$, with the action of every $a\in W(\mathbf F_{p^2})$, and with the action of $\varpi$, for which there is a $c\in\mathbf N$ with $\theta\bigl((\rho_\kappa)_*(p^{c+n'}f)\bigr)=(\rho'_\kappa)_*(p^{c+n}f)$ for all $f$ in the Cartier module of $\Psi$.
--
--   This is the Cartier–Dieudonné module form of the injectivity step in the Čerednik–Drinfeld comparison: an isomorphism of the Drinfeld data attached to two admissible rigidified special formal $\mathcal O_D$-modules over an algebraically closed field produces an isomorphism of their Cartier modules respecting all the operators and matching the rigidifications up to a bounded power of $p$. Its conclusion is exactly the hypothesis list of the criterion deducing that the two rigidified data are themselves isomorphic, which is the declaration citing it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {κ : Type} [Field κ] [IsAlgClosed κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q') :
    ∃ (Ψ : MvFormalGroup 2 κ) (_ : Ψ.IsComm) (ρκ : Ψ.Hom t.X.F) (ρκ' : Ψ.Hom t'.X.F)
      (θ : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p t'.X.F),
      Series.map (Ideal.Quotient.mk (pIdeal p κ)) ρκ.toPowerSeries = t.ρ ∧
      Series.map (Ideal.Quotient.mk (pIdeal p κ)) ρκ'.toPowerSeries = t'.ρ ∧
      Function.Bijective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) = MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) = MvFormalGroup.CartierModule.verschiebung (θ f)) ∧
      (∀ (a : κ) f, θ (MvFormalGroup.CartierModule.homothety a f) = MvFormalGroup.CartierModule.homothety a (θ f)) ∧
      (∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct (t.X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (t'.X.actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct t.X.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct t'.X.varpiEnd (θ f)) ∧
      ∃ c : ℕ, ∀ f : MvFormalGroup.CartierModule p Ψ,
        θ (MvFormalGroup.CartierModule.map ρκ (p ^ (c + t'.n) • f)) =
          MvFormalGroup.CartierModule.map ρκ' (p ^ (c + t.n) • f) := by sorry
