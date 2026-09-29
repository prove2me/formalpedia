-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/668318e9-fe76-59d3-b539-8ede079356ea
-- title:
--   Uniqueness of the Cartier quadruple as a Drinfeld datum
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{p^2}$ for the Witt vectors of $\mathbb{F}_{p^2}$. Let $O$ be a commutative ring with a ring map $\iota : \mathbb{Z}_{p^2} \to O$, and let $\Phi$ be a formal $\mathcal{O}_D$-module of dimension $2$ over $O/pO$ (a commutative formal group law in two variables with an action of $\mathbb{Z}_{p^2}$ and an endomorphism $\varpi$ satisfying $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$), taken with respect to the induced map $\bar\jmath = \iota$ followed by reduction, `Rigidified.jbar ι`. Assume: $\Phi$ is special, i.e. $\mathrm{Lie}\,\Phi$ is the direct sum of the two eigen-submodules `lieZero` and `lieOne`, each invertible; $\Phi$ has height $4$, i.e. the kernel of $[p]$ has degree $p^4$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (hypothesis `hcΦ`), so that $\Phi$ yields graded Cartier module data $D_\Phi$; and $r_\Phi : \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ is an additive map which, for every canonical $L$-map $L$ on $D_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ eta-piece of $L$. Let $B$ be a noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : O \to B$ a ring map, and $t = (X, n, \rho)$ a rigidified object over $B$ which is admissible for $\iota, \psi$: $X$ is special and of height $4$ over $B$ for the structure map $\psi \circ \iota$, and $\rho$ is an isogeny of height $4n$ from $\Phi$ base-changed along $\psi$ to the reduction $\bar X$. Finally let $Q$ and $Q'$ be Drinfeld data over $B$ for $\mathbb{Z}_p \subset \mathbb{Q}_p$ with uniformiser $p$ (families of full lattices $N_0(x) \le N_1(x) \subset \mathbb{Q}_p^2$ over $\mathrm{Spec}\,B$ with the openness conditions, invertible $B$-modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ composing to multiplication by $p$, and compatible stalk maps $u_0, u_1$), and suppose both are Cartier quadruples for $t$ with respect to $\iota, h_{c\Phi}, r_\Phi, \psi$, that is: $\rho$ is an $\mathcal{O}_D$-homomorphism, there are $B$-linear isomorphisms $T_0 \cong (\mathrm{Lie}\,X)_0$ and $T_1 \cong (\mathrm{Lie}\,X)_1$ interchanged by $\Pi_0, \Pi_1$ and the linear part of $\varpi$ on $\mathrm{Lie}\,X$, and at every prime $x$ of $B$ the lattices $N_0(x), N_1(x)$ consist exactly of those $v$ admitting an eta-section in degree $0$, respectively $1$, over some localisation $B_f$ with $f \notin x$, the stalk maps $u_0, u_1$ being determined on such $v$ by the associated tangent data. Then $Q$ and $Q'$ are isomorphic as Drinfeld data.
--
--   This is the uniqueness half of the Čerednik–Drinfeld dictionary between admissible rigidified special formal $\mathcal{O}_D$-modules over a $p$-nilpotent base and Drinfeld data of lattice chains: the Cartier quadruple attached to $t$ is canonical. It is used downstream to identify the quadruple attached to a $\Pi$-translate and to show that period values are well defined and do attach a quadruple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t.IsCartierQuadruple ι hcΦ rΦ ψ Q') :
    Q.IsIsomorphic Q' := by sorry
