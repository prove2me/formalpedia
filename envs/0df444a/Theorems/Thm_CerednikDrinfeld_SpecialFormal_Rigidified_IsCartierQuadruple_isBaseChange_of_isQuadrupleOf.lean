-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isBaseChange_of_isQuadrupleOf
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChange_of_isQuadrupleOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/54898def-0193-54e6-9cc2-eea915d3d80d
-- title:
--   Cartier quadruples: base change of the associated Deligne datum
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota \colon \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $O_D$-module over $O/pO$ which is special for $\bar{\jmath} = \iota$ followed by reduction (its weight-$0$ and weight-$1$ Lie parts are complementary and invertible) and of height $4$. Assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data $D_\Phi$, and let $r_\Phi \colon \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ be an additive map which, for every canonical $L$-map $L$ on $D_\Phi$, maps the whole of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$, $B'$ be Noetherian $\mathbb{Z}_p$-algebras in which $p$ is nilpotent, with structure homomorphisms $\psi \colon O \to B$, $\psi' \colon O \to B'$, and let $f \colon B \to B'$ be a $\mathbb{Z}_p$-algebra homomorphism with $f \circ \psi = \psi'$. Let $t$ be a rigidified object over $B$ (a formal $O_D$-module $t.X$, an integer $n$, and a series $\rho$ over $B/pB$) which is admissible for $\iota, \psi$: $t.X$ is special of height $4$ and $\rho$ is an isogeny of height $4n$. Let $Q$, $Q'$ be Drinfeld data over $B$, $B'$ for the uniformiser $p \in \mathbb{Z}_p \subset \mathbb{Q}_p$ such that $Q$ is a Cartier quadruple for $t$ and $Q'$ one for the base change $t \otimes_B B'$, and let $d$, $d'$ be Deligne data over $B$, $B'$ of which $Q$, $Q'$ are the associated Drinfeld quadruples, i.e. at every prime $x$ the edge nondegeneracy condition holds for the lattices $L_0(x) \le L_1(x)$ and the kernels of $u_0(x)$, $u_1(x)$ are the lines of the localised Deligne datum at those lattices. Then $d'$ is the base change of $d$ along $f$: for every full $\mathbb{Z}_p$-lattice $M$ in $\mathbb{Q}_p^2$, the line $d'.\mathrm{line}\,M$ is the $B'$-span of the image of $d.\mathrm{line}\,M$ under $f \otimes \mathrm{id}_M$.
--
--   This is the base-change compatibility in the Čerednik–Drinfeld comparison: the Cartier-theoretic quadruple attached to a rigidified special formal $O_D$-module is functorial in the base, and the statement records this on the level of the Deligne data that the Drinfeld quadruples determine, since it is there that a base-change predicate is available. It feeds the period-map and descent statements, among them [`CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isBaseChange`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isBaseChange) and the construction of Drinfeld data over covers of an admissible rigidified object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isBaseChange_of_isQuadrupleOf.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChange_of_isQuadrupleOf
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
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadruple ι hcΦ rΦ ψ' Q')
    (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d' : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (hd : Q.IsQuadrupleOf d) (hd' : Q'.IsQuadrupleOf d') :
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f d d' := by sorry
