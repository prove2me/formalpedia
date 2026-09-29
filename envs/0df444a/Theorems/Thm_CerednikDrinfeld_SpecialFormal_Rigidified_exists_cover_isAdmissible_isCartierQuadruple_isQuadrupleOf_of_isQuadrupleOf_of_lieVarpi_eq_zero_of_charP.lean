-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero_of_charP
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/46d75441-4c76-5098-96bb-3ca88d40e566
-- title:
--   Local realisation of Drinfeld quadruples in characteristic p
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ (a commutative two-dimensional formal group with an action of $W(\mathbb F_{p^2})$ and an operator $\varpi$ satisfying $\varpi^2=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$) over $W(k)/pW(k)$, with $\bar\jmath$ the reduction of $\iota$. Assume: $\Phi$ is special for $\bar\jmath$, meaning $\mathrm{Lie}_0$ and $\mathrm{Lie}_1$ are complementary and each invertible; $\Phi$ has height $4$, i.e. the action of $p$ has kernel of degree $p^4$; every $m$ in $\Phi.\mathrm{lieZero}(\bar\jmath)$ satisfies $\mathrm{lieVarpi}(m)=0$; the Teichmüller eigen-subgroups $\mathrm{gradedPiece}\,0$ and $\mathrm{gradedPiece}\,1$ of the Cartier module of $\Phi$ are complementary, via $hc_\Phi$; and $r_\Phi\colon(\mathbb Z_p)^2\to N$ is an additive map into the $N$-module of the graded Cartier module data $D_\Phi$ attached to $\Phi$, $\bar\jmath$, $hc_\Phi$, which for every canonical $L$-map $L$ on $D_\Phi$ maps $(\mathbb Z_p)^2$ bijectively onto the degree-$0$ eta-piece $\mathrm{etaPiece}\,L\,0$. Then for every Noetherian commutative $\mathbb Z_p$-algebra $B$, every ring homomorphism $\psi\colon W(k)\to B$, with $p$ nilpotent in $B$ and $p=0$ in $B$, and every Drinfeld datum $Q$ and Deligne datum $d$ over $B$ for $K=\mathbb Q_p$, $\pi=p$, such that $Q$ is the quadruple of $d$ (at each prime $x$ of $B$, edge-nondegeneracy of $d$ at $Q.L_0(x)\subseteq Q.L_1(x)$ and $\ker u_0(x)$, $\ker u_1(x)$ the corresponding lines), there are finitely many $f_1,\dots,f_n\in B$ generating the unit ideal such that for each $i$ and each Noetherian $\mathbb Z_p$-algebra $L$ which is a localisation of $B$ away from $f_i$ (compatibly with the towers) in which $p$ is nilpotent, there exist a rigidification $t$ over $L$ (a formal $\mathcal O_D$-module $t.X$ over $L$, an integer $t.n$, and a series $t.\rho$ over $L/pL$), a Deligne datum $d_L$ and a Drinfeld datum $Q_L$ over $L$ with: $t$ admissible for $\iota$ and $L\circ\psi$, i.e. $t.X$ special for the structure map, of height $4$, and $t.\rho$ an isogeny of height $4\,t.n$ from the base change of $\Phi$ to $\bar t.X$; $t$ a Cartier quadruple for $\iota$, $hc_\Phi$, $r_\Phi$ and $Q_L$; $Q_L$ the quadruple of $d_L$; and $d_L$ the base change of $d$ along $B\to L$, i.e. for every full lattice $M$ the line of $d_L$ at $M$ is spanned by the image of the line of $d$ at $M$.
--
--   This is the Zariski-local existence (surjectivity) half of Drinfeld's classification of special formal $\mathcal O_D$-modules by quadruples of lattice-type data, restricted to bases on which $p$ vanishes; the remaining $p$-nilpotent cases are handled separately by lifting. It feeds the construction of admissible rigidifications with prescribed period value, [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isPeriodValue_of_isAlgClosed_of_lieZero_le_ker`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isPeriodValue_of_isAlgClosed_of_lieZero_le_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero_of_charP.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero_of_charP
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    :
    (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (hp0 : (p : B) = 0)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B), Q.IsQuadrupleOf d →
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] B L]
        [IsLocalization.Away (f i) L] (hL : IsNilpotent (p : L)),
        ∃ (t : Rigidified p Φ L) (dL : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) L)
          (QL : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) L),
          t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
          t.IsCartierQuadruple ι hcΦ rΦ ((algebraMap B L).comp ψ) QL ∧ QL.IsQuadrupleOf dL ∧
          DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) (IsScalarTower.toAlgHom ℤ_[p] B L) d dL) := by sorry
