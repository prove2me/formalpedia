-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/6cea0ba8-c62b-5968-bf13-e6eb49c429d1
-- title:
--   Cartier-module criterion for isomorphism of rigidified formal mathcal O_D-modules
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring and $\Phi$ a formal $\mathcal O_D$-module over $O/pO$ (that is, a commutative two-dimensional formal group law equipped with series endomorphisms $\mathrm{act}(a)$ for $a$ in the Witt vectors $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$ and a series $\varpi$ with $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$), used only as the reference object for rigidifications. Let $L$ be a perfect field of characteristic $p$ and let $t=(X,n,\rho)$, $t'=(X',n',\rho')$ be rigidified objects over $L$ relative to $\Phi$: formal $\mathcal O_D$-modules $X,X'$ over $L$, natural numbers $n,n'$, and pairs of power series $\rho,\rho'$ over $L/pL$. Let $\Psi$ be a commutative two-dimensional formal group law over $L$ and $\rho_L\colon\Psi\to X$, $\rho'_L\colon\Psi\to X'$ homomorphisms of formal group laws whose coefficientwise reductions modulo the ideal $(p)$ of $L$ are $\rho$ and $\rho'$. Assume given an additive bijection $\theta$ from the Cartier module of $X$ to that of $X'$ commuting with the Frobenius operator, with the Verschiebung operator, with the homothety by every $a\in L$, with the operators induced by $\mathrm{act}(a)$ for every $a\in\mathbb Z_{p^2}$ and by $\varpi$ (matching those of $X$ with those of $X'$), and such that for some $c\in\mathbb N$ one has $\theta\bigl((\rho_L)_*(p^{c+n'}f)\bigr)=(\rho'_L)_*(p^{c+n}f)$ for every element $f$ of the Cartier module of $\Psi$. Then $t$ and $t'$ are isomorphic as rigidified objects: there are series $u,v$ over $L$ and an $m\in\mathbb N$ such that $u$ is a homomorphism of formal $\mathcal O_D$-modules $X\to X'$, $v$ one $X'\to X$, $v\circ u$ and $u\circ v$ are the identity, and $\mathrm{act}(p^{m+n'})\circ(\bar u\circ\rho)=\mathrm{act}(p^{m+n})\circ\rho'$ on the base change of $X'$ to $L/pL$, $\bar u$ being the reduction of $u$.
--
--   This is the Cartier–Dieudonné criterion identifying two rigidified formal $\mathcal O_D$-modules over a perfect field once their Cartier modules, with the $\mathcal O_D$-operators and the rigidifications, are matched by a bijection; it is the injectivity mechanism for Drinfeld's moduli problem at geometric points. The two inputs used are the construction of a homomorphism of formal group laws out of an operator-equivariant map of Cartier modules over a perfect field, [`MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing`](thm.html#MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing), and the faithfulness statement [`MvFormalGroup.CartierModule.eq_of_map_eq`](thm.html#MvFormalGroup.CartierModule.eq_of_map_eq); the result feeds the comparison of Cartier quadruples in [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq
    (p : ℕ) [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (L : Type u) [Field L] [CharP L p] [PerfectRing L p]
    (t t' : Rigidified p Φ L)
    (Ψ : MvFormalGroup 2 L) [Ψ.IsComm] (ρL : Ψ.Hom t.X.F) (ρL' : Ψ.Hom t'.X.F)
    (hρL : Series.map (Ideal.Quotient.mk (pIdeal p L)) ρL.toPowerSeries = t.ρ)
    (hρL' : Series.map (Ideal.Quotient.mk (pIdeal p L)) ρL'.toPowerSeries = t'.ρ)
    (θ : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p t'.X.F)
    (hθ : Function.Bijective θ)
    (hθF : ∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
      MvFormalGroup.CartierModule.frobenius (θ f))
    (hθV : ∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
      MvFormalGroup.CartierModule.verschiebung (θ f))
    (hθh : ∀ (a : L) f, θ (MvFormalGroup.CartierModule.homothety a f) =
      MvFormalGroup.CartierModule.homothety a (θ f))
    (hθa : ∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct (t.X.actEnd a) f) =
      MvFormalGroup.CartierModule.endAct (t'.X.actEnd a) (θ f))
    (hθϖ : ∀ f, θ (MvFormalGroup.CartierModule.endAct t.X.varpiEnd f) =
      MvFormalGroup.CartierModule.endAct t'.X.varpiEnd (θ f))
    (hθρ : ∃ c : ℕ, ∀ f : MvFormalGroup.CartierModule p Ψ,
      θ (MvFormalGroup.CartierModule.map ρL (p ^ (c + t'.n) • f)) =
        MvFormalGroup.CartierModule.map ρL' (p ^ (c + t.n) • f)) :
    t.IsIsomorphic t' := by sorry
