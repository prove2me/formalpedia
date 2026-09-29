-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a7e18834-c52a-5cdb-9e15-9fe2f3ac6831
-- title:
--   Critical-index extension of an η-piece bijection
-- statement:
--   Throughout, $p$ is a prime, $\mathbb Z_{p^2}$ denotes `Zp2 p` $= W(\mathbb F_{p^2})$, and a `FormalODModule p B` is a $2$-dimensional commutative formal group law $F$ over $B$ together with an action `act` of $\mathbb Z_{p^2}$ by formal group endomorphisms and a further endomorphism `varpi` satisfying $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$. For such an $X$ and a ring homomorphism $j:\mathbb Z_{p^2}\to B$, `gradedPiece X j n` is the additive subgroup of the Cartier module $M=\,$`CartierModule p X.F` of those $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau(c)))f=\tau\bigl(j(\tau(c))^{p^n}\bigr)\cdot f$ for all $c\in\mathbb F_{p^2}$, $\tau$ denoting Teichmüller lifts; when the pieces for $n=0,1$ are complementary, `toGradedCartierModuleData` packages $M$ with its Frobenius $F$, its integral Verschiebung $V$, the $W(B)$-linear operator induced by `varpi`, and these two pieces. For such data $D$, `NMod` is the quotient of $D.M\times D.M^{\sigma}$ by the submodule `nRel`, with `nMk` the induced additive map from $D.M\times D.M$, `vRange` the image of $V$, `LieQuot` $=D.M/VD.M$, `nPiece i` the image under `nMk` of the $i$-th piece times itself, and `etaPiece L hL i` the intersection of `D.eta L hL` with `nPiece i`; `IsCanonicalLMap L` asserts that $L$ is a Cartier $L$-map which, along a surjection from a special graded Cartier module datum over a $p$-torsion-free ring, is induced by an $L$-map upstairs.
--
--   Base data over $W(k)$. Let $k$ be an algebraically closed field of characteristic $p$, let $\iota:\mathbb Z_{p^2}\to W(k)$ be a ring homomorphism, write $\bar\jmath$ for the composite of $\iota$ with the quotient map $W(k)\to W(k)/pW(k)$, and let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/pW(k)$. The hypotheses on $\Phi$ are: `hΦ`, that $\Phi$ is special for $\bar\jmath$, i.e. `lieZero` and `lieOne` are complementary submodules of the Lie module and both are invertible; `hΦ4`, that $\Phi$ has height $4$, i.e. $\mathrm{act}(p)$ has kernel of degree $p^4$; `h0Φ`, that `lieZero` for $\bar\jmath$ is contained in the kernel of `lieVarpi`, the linear part of $\varpi$ acting on the Lie module; and `hcΦ`, that the graded pieces of degrees $0$ and $1$ of $\Phi$ for $\bar\jmath$ are complementary. Write $D_\Phi$ for the resulting graded Cartier module datum. Further data are an additive map $r_\Phi:(\mathrm{Fin}\,2\to\mathbb Z_p)\to D_\Phi.\mathrm{NMod}$, the hypothesis `hLΦ` that a canonical $L$-map for $D_\Phi$ exists, and the hypothesis `hrΦ` that for every canonical $L$-map $L$ of $D_\Phi$ the map $r_\Phi$ carries all of $\mathrm{Fin}\,2\to\mathbb Z_p$ bijectively onto `etaPiece L … 0`.
--
--   Base field and rigidified objects. Let $\kappa$ be an algebraically closed field of characteristic $p$ which is a $\mathbb Z_p$-algebra, and $\psi:W(k)\to\kappa$ a ring homomorphism. Let $t=(X,n,\rho)$ and $t'=(X',n',\rho')$ be objects of `Rigidified p Φ κ`, each consisting of a formal $\mathcal O_D$-module over $\kappa$, a natural number and a series over $\kappa/p\kappa$. The hypotheses `ht` and `ht'` state admissibility of $t$ and $t'$: the underlying module is special for the structure map attached to $\iota$ and $\psi$, has height $4$, and $\rho$ (respectively $\rho'$) is an isogeny of height $4n$ (respectively $4n'$) from the reduction `t.Φbar ψ` of $\Phi$ along $\psi$ to the reduction of $X$ (respectively $X'$) modulo $p$. The hypotheses `hOD` and `hOD'` state that $\rho$ and $\rho'$ are homomorphisms of formal $\mathcal O_D$-modules, i.e. homomorphisms of formal group laws commuting with the $\mathbb Z_{p^2}$-actions and with $\varpi$.
--
--   Drinfeld data. Let $Q,Q'$ be Drinfeld data over $\kappa$ for the uniformiser $p\in\mathbb Z_p$ inside $\mathbb Q_p$: families of full $\mathbb Z_p$-lattices $N_0(x)\subseteq N_1(x)$ in $\mathbb Q_p^2$ indexed by the points $x$ of $\operatorname{Spec}\kappa$ with $pN_1(x)\subseteq N_0(x)$ and the indicated openness conditions, together with invertible $\kappa$-modules $T_0,T_1$, maps $\Pi_0,\Pi_1$ between them composing to multiplication by $p$ in either order, and comparison maps $u_0,u_1$ from the base-changed lattices to the stalks of $T_0,T_1$, compatible with inclusions and with multiplication by $p$. The hypotheses `hQ` and `hQ'` state that $t$ with $Q$, respectively $t'$ with $Q'$, form a Cartier quadruple relative to $\iota$, `hcΦ`, $r_\Phi$ and $\psi$: the relevant $\rho$ is a homomorphism of formal $\mathcal O_D$-modules, $T_0$ and $T_1$ are identified $\kappa$-linearly with `lieZero` and `lieOne` of the underlying module in a way intertwining $\Pi_0,\Pi_1$ with `lieVarpi`, and for each point $x$ of $\operatorname{Spec}\kappa$ the lattices $N_0(x)$ and $N_1(x)$ consist exactly of those vectors admitting, on some basic Zariski neighbourhood of $x$ determined by an element $f\notin x$ and choices of gradings and of a canonical $L$-map, an $\eta$-section in the sense of `IsEtaSection` of index $0$, respectively $1$, together with compatibility clauses relating the maps $u_0,u_1$ of the datum to the canonical maps of the graded Cartier data modulo `vRange` (these further clauses are summarised here). Finally `hiso` states that $Q$ and $Q'$ are isomorphic as Drinfeld data.
--
--   Gradings, $L$-maps and index. Write $g=\,$`Rigidified.awayHom (1 : κ)` for the localisation of $\kappa$ at the powers of $1$, with target `Rigidified.Baway (1 : κ)`, and let `t.XS g`, `t'.XS g` be the associated formal $\mathcal O_D$-modules over that ring and `Rigidified.jS ι ψ g` the associated homomorphism from $\mathbb Z_{p^2}$. The hypotheses `hc`, `hc'` state that the graded pieces of degrees $0$ and $1$ of `t.XS g`, respectively `t'.XS g`, for `jS ι ψ g` are complementary; `hcb`, `hcb'` state the same for the reductions `t.XbarS g`, `t'.XbarS g` with respect to `jSbar ι ψ g`; and `hcΦg` states it for `PhibarS ψ g`, the base change of $\Phi$ along $\psi$ and $g$, with respect to `jPhiS ι ψ g`. Let $D$ and $D'$ be the graded Cartier module data of `t.XS g` and `t'.XS g` furnished by `hc` and `hc'`, and let $L$, $L'$ be additive maps $D.M\to D.\mathrm{NMod}$ and $D'.M\to D'.\mathrm{NMod}$ satisfying `IsCanonicalLMap` (`hL`, `hL'`). Let $i\in\{0,1\}$. The hypotheses `hi` and `hi'` express criticality of the index $i$: every element $m$ of the $i$-th graded piece of `t.XS g` (respectively of `t'.XS g`) satisfies $\varpi_*m=Vy$ for some $y$ in the corresponding Cartier module.
--
--   Comparison maps. Let $\theta_\eta$ be an additive map from `etaPiece L … i` of $D$ to `etaPiece L' … i` of $D'$, and $\tau$ a $W(\mathrm{Baway}(1))$-linear map $D.\mathrm{LieQuot}\to D'.\mathrm{LieQuot}$. The hypotheses are `hθη`, that $\theta_\eta$ is bijective; `hτ`, that $\tau$ is injective; and `hcompat`, that for all $m\in D.M$, $m'\in D'.M$ and every proof that $D.\mathrm{nMk}(m,0)$ lies in `etaPiece L … i`, if the image of $\langle D.\mathrm{nMk}(m,0)\rangle$ under $\theta_\eta$, viewed in $D'.\mathrm{NMod}$, equals $D'.\mathrm{nMk}(m',0)$, then $\tau$ sends the class of $m$ modulo `vRange` to the class of $m'$ modulo `vRange`.
--
--   Conclusion. There exists an additive map $\theta$ from `CartierModule p (t.XS g).F` to `CartierModule p (t'.XS g).F` such that: $\theta$ is bijective; $\theta(Ff)=F(\theta f)$ for all $f$; $\theta(Vf)=V(\theta f)$ for all $f$, with $V$ the integral Verschiebung; $\theta(w\cdot f)=w\cdot\theta f$ for all $w\in W(\mathrm{Baway}(1))$ and all $f$; $\theta$ commutes with the action of $\mathrm{actEnd}(a)$ for every $a\in\mathbb Z_{p^2}$, that is $\theta(\mathrm{endAct}((t.XS\,g).\mathrm{actEnd}\,a)f)=\mathrm{endAct}((t'.XS\,g).\mathrm{actEnd}\,a)(\theta f)$; $\theta$ commutes with the action of `varpiEnd`, that is $\theta(\mathrm{endAct}((t.XS\,g).\mathrm{varpiEnd})f)=\mathrm{endAct}((t'.XS\,g).\mathrm{varpiEnd})(\theta f)$; and $\theta$ extends $\theta_\eta$ in the sense that for every $m\in D.M$ with $D.\mathrm{nMk}(m,0)$ in `etaPiece L … i`, the image of $\langle D.\mathrm{nMk}(m,0)\rangle$ under $\theta_\eta$, viewed in $D'.\mathrm{NMod}$, equals $D'.\mathrm{nMk}(\theta m,0)$.
--
--   This is the critical-index extension step in the Čerednik–Drinfeld uniformisation theory of special formal $\mathcal O_D$-modules, as in Boutot–Carayol, chapter II, §5: at a critical index over an algebraically closed field an additive bijection of $\eta$-pieces compatible with an injective map of Lie quotients is promoted to an isomorphism of the full Cartier modules respecting $F$, $V$, the Witt-vector scalars, the $\mathbb Z_{p^2}$-action and $\varpi$. It is used in the proof of [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isIsomorphic_of_isAlgClosed_of_lieZero_le_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
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
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ (t.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F,
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd m)
    (hi' : ∀ m ∈ (t'.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd m)
    (θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot)
    (hθη : Function.Bijective θη) (hτ : Function.Injective τ)
    (hcompat : ∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
        ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0) →
        τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m') :
    ∃ θ : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F →+ MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
      Function.Bijective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) = MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) = MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (w : WittVector p (Rigidified.Baway (1 : κ))) f, θ (w • f) = w • θ f) ∧
      (∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct ((t.XS (Rigidified.awayHom (1 : κ))).actEnd a) f) =
        MvFormalGroup.CartierModule.endAct ((t'.XS (Rigidified.awayHom (1 : κ))).actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd f) =
        MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd (θ f)) ∧
      (∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
        ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (θ m, 0)) := by sorry
