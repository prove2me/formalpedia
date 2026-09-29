-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isBaseChangeAlong
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/05e2ac76-179f-5cc1-a14c-8303ab297de8
-- title:
--   Cartier quadruples of rigidified modules commute with base change
-- statement:
--   Let $p$ be a prime, let $O$ be a commutative ring with a ring homomorphism $\iota\colon \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$ (a commutative two-dimensional formal group with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$). Assume $\Phi$ is special for the reduced map $\bar\iota$ (its Lie algebra splits as the direct sum of the weight-$0$ and weight-$1$ pieces, both invertible), that $\Phi$ has height $4$, that the weight-$0$ and weight-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (witnessed by $h_{c\Phi}$), and let $r_\Phi\colon \mathbb{Z}_p^2 \to N(M_\Phi)$ be an additive map which, for every canonical $L$-map $L$ on the associated graded Cartier module data, maps all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece attached to $L$. Let $B$, $B'$ be Noetherian $\mathbb{Z}_p$-algebras in which $p$ is nilpotent, equipped with structure homomorphisms $\psi\colon O \to B$, $\psi'\colon O \to B'$, and let $f\colon B \to B'$ be a $\mathbb{Z}_p$-algebra homomorphism with $f \circ \psi = \psi'$. Let $t = (X, n, \rho)$ be a rigidified triple over $B$ which is admissible for $(\iota,\psi)$, namely $X$ is special of height $4$ and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to that of $X$. Let $Q$ be a Drinfeld datum over $B$ for the uniformiser $p$ and $Q'$ one over $B'$, and suppose $Q$ is a Cartier quadruple for $t$ and $Q'$ is a Cartier quadruple for the base change $t \otimes_B B'$ (both with respect to $\iota$, $h_{c\Phi}$, $r_\Phi$ and the respective structure map): that is, the relevant reduction map is a homomorphism of formal $\mathcal{O}_D$-modules, the invertible modules $T_0$, $T_1$ are identified with the two graded pieces of $\mathrm{Lie}$ in a way intertwining $\Pi_0$, $\Pi_1$ with the action of $\varpi$, and at each prime the lattices $N_0$, $N_1$ and the maps $u_0$, $u_1$ are described by $\eta$-sections over basic open sets and the canonical maps of the localised graded Cartier module data. Then $Q'$ is a base change of $Q$ along $f$: there exist $f$-semilinear maps $\tau_0\colon T_0 \to T_0'$ and $\tau_1\colon T_1 \to T_1'$ whose ranges generate $T_0'$, $T_1'$ over $B'$ and which commute with $\Pi_0$ and $\Pi_1$, the lattices satisfy $N_i'(x') = N_i(f^{-1}(x'))$ for all $x' \in \operatorname{Spec} B'$ and $i = 0,1$, and whenever $u_i$ at $f^{-1}(x')$ sends $1 \otimes v$ to $t/s$ then $u_i'$ at $x'$ sends $1 \otimes v$ to $\tau_i(t)/f(s)$.
--
--   This is the naturality of Drinfeld's construction on the category of $p$-nilpotent Noetherian $\mathbb{Z}_p$-algebras: the quadruple $(N, T, \Pi, u)$ attached to a rigidified special formal $\mathcal{O}_D$-module of height $4$ is compatible with base change of the base ring. It is used in the comparison of the moduli functor of rigidified special formal $\mathcal{O}_D$-modules with the Drinfeld functor of quadruples, and is cited in the construction of the associated isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isBaseChangeAlong.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : O →+* B')
    (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadruple ι hcΦ rΦ ψ' Q') :
    Q.IsBaseChangeAlong f Q' := by sorry
