-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
-- name    : CerednikDrinfeld.FormalODModule.smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/54625b38-d2ae-5490-af01-71421e72fecd
-- title:
--   Node normalisation of the rigidification numerator propagates under base change
-- statement:
--   Throughout, $p$ is a prime, $k$ an algebraically closed field of characteristic $p$, $O:=W(k)$ the ring of Witt vectors of $k$, $\bar O:=O/pO$, and $\mathbb{Z}_{p^2}:=W(\mathbb{F}_{p^2})$ (the type `Zp2 p`). A ring homomorphism $\iota:\mathbb{Z}_{p^2}\to O$ is fixed, and $\bar\iota$ denotes the composite of $\iota$ with $O\to\bar O$.
--
--   **The object $\Phi$ and the numerator $r_\Phi$.** $\Phi$ is a formal $\mathcal O_D$-module over $\bar O$: a two-dimensional commutative formal group law $\Phi.F$, an action `act` of $\mathbb{Z}_{p^2}$ by endomorphisms of $\Phi.F$, and an endomorphism $\varpi$ with $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$. Four hypotheses are imposed on it. `hΦ` asserts that $\Phi$ is special for $\bar\iota$, i.e. the submodules `lieZero` and `lieOne` of the tangent module are complementary and each is an invertible $\bar O$-module, where $\mathrm{lieZero}(\bar\iota)=\bigcap_{a}\ker(\mathrm{lieAct}(a)-\bar\iota(a)\,\mathrm{id})$. `hΦ4` asserts that $\mathrm{act}(p)$ has kernel of degree $p^4$. `h0Φ` asserts that $\mathrm{lieZero}(\bar\iota)$ is contained in the kernel of `lieVarpi`, the linear part of $\varpi$ acting on the tangent module. `hcΦ` asserts that the graded pieces of degrees $0$ and $1$ are complementary additive subgroups of the Cartier module $M(\Phi):=$ `CartierModule p Φ.F`, the degree-$n$ piece consisting of those curves $f$ with $\mathrm{act}(\tau c)_*f=[\bar\iota(\tau c)^{p^n}]f$ for all $c\in\mathbb{F}_{p^2}$ ($\tau$ the Teichmüller lift, $[\cdot]$ homothety). Out of `hcΦ` one forms the graded Cartier module data $D_\Phi:=\Phi.\mathrm{toGradedCartierModuleData}(\bar\iota,hc\Phi)$, with underlying module $M(\Phi)$, Frobenius, integral Verschiebung, the $\varpi$-action, and the two graded submodules as pieces. Finally $r_\Phi:\mathbb{Z}_p^{2}\to N(D_\Phi)$ is an additive map into the $N$-module $N(D_\Phi)=(M\times\Sigma)/\mathrm{nRel}$, and `hrΦ` requires: for every additive map $L:M(\Phi)\to N(D_\Phi)$ which is a canonical $L$-map (a Cartier $L$-map which, along a surjection from a ring without $p$-torsion carrying special graded Cartier module data, is the base change of a Cartier $L$-map there), $r_\Phi$ restricted to all of $\mathbb{Z}_p^{2}$ is a bijection onto the subgroup `etaPiece L _ 0`, the intersection of the subgroup `eta` attached to $L$ with the degree-$0$ piece of $N(D_\Phi)$.
--
--   **The matrix $g$.** An element $g$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ is given, together with the hypothesis `hg` that its matrix is the diagonal matrix with entries $p$ and $1$. It does not occur in the conclusion.
--
--   **The edge family.** $X$ is a formal $\mathcal O_D$-module over the edge chart ring $E:=$ `EdgeFamily.edgeRingCharP p (O/pO)`, the localisation `chartERing` of the edge quotient ring away from its discriminant, and $\gamma_0,\gamma_1\in M(X)$. Write $j_E$ for the structure map $\mathbb{Z}_{p^2}\to E$ obtained from $\iota$ followed by $O\to\bar O\to E$. The hypothesis `hγ` says that $\gamma$ is a homogeneous $V$-basis: $\gamma_i$ lies in the graded piece of degree $i$ for $j_E$, and the matrix $(\mathrm{tangent}(\gamma_i)_l)_{i,l}$ has unit determinant. The hypothesis `hγa` says that $\gamma$ has the edge-ring constants as structure constants: for each $i$ and each $N$ there is $h\in M(X)$ with $\varpi_*\gamma_i=\sum_{m<N}V^{m}\!\left([a_{m,i}]\gamma_{\pi(m,i)}\right)+V^{N}h$, where $\pi(m,i)=(m+i+1)\bmod 2$ and $a_{m,0}$, $a_{m,1}$ are the branch constants of $E$ in $\eta$, respectively in $\xi$. Furthermore `hXs` says that $X$ is special for $j_E$ and `hX4` that $\mathrm{act}(p)$ on $X$ has kernel of degree $p^4$.
--
--   **The node point and the rigidified object.** $f_0:E\to\bar O$ is a ring homomorphism with `hf₀`: $f_0$ retracts the structure map $\bar O\to E$; `hf₀ξ`: $f_0(\xi)=0$; and `hf₀η`: $f_0(\eta)=0$. Given $m\in\mathbb{N}$ and $\rho_0\in$ `Series` $\bar O$, the hypothesis `hρ₀` says that $\rho_0$ is an isogeny of height $4m$ from $\Phi$ to $X^0:=X\otimes_{f_0}\bar O$, i.e. an $\mathcal O_D$-homomorphism whose kernel has degree $p^{4m}$. Put $t_0:=$ `Rigidified.mk` $X^0\ m\ (\rho_0\bmod p)$, the rigidified datum over $\bar O$ with formal module $X^0$, integer $m$, and series the image of $\rho_0$ in $\bar O/p\bar O$. The hypothesis `hOD₀` says that the series of $t_0$ is an $\mathcal O_D$-homomorphism from $\Phi$ base-changed to $\bar O/p\bar O$ to $\bar X^0:=X^0\bmod p$; `hcb` says that the degree-$0$ and degree-$1$ graded pieces of $t_0.\mathrm{XbarS}(\mathrm{id})$ for $j_{\bar S}$ are complementary; `hcΦg` says the same for the corresponding base change of $\Phi$ with its structure map.
--
--   **The normalisation at the node.** With $a\in\mathbb{N}$, the hypothesis `hN` states that for $i=0,1$,
--   $$p^{a}\cdot r(e_i)=p^{a+m}\cdot c_i,$$
--   where $r:=$ `Rigidified.rigidNum` $\iota\ hc\Phi\ r_\Phi$ for the quotient map $O\to\bar O$, the datum $t_0$, the witnesses `hOD₀`, `hcb`, `hcΦg` and $g=\mathrm{id}_{\bar O}$ — that is, $r_\Phi$ followed by the map of $N$-modules induced by the base change $M(\Phi)\to M(\bar\Phi)$ and then by the map induced by the series of $t_0$ — $e_i=$ `Pi.single i 1` is the $i$-th standard vector of $\mathbb{Z}_p^{2}$, and, writing $D$ for the graded Cartier module data of $t_0.\mathrm{XbarS}(\mathrm{id})$ attached to `hcb` and $\beta_0$ for the composite base change of Cartier modules along $f_0$, then along $\bar O\to\bar O/p\bar O$, then along the reduction of $\mathrm{id}_{\bar O}$: $c_0=D.\mathrm{nMk}(\beta_0(\gamma_0),0)$ and $c_1=D.\mathrm{nVarpi}\bigl(D.\mathrm{nMk}(\beta_0(\gamma_1),0)\bigr)$.
--
--   **The further base change.** $S$ is a commutative ring, $y_0:\bar O\to S$ a ring homomorphism, $S'$ a commutative ring and $g_S:S\to S'$ a ring homomorphism. Writing $t_0\otimes_{y_0}S:=t_0.\mathrm{map}\,y_0$ (formal module $X^0\otimes_{y_0}S$, the same integer $m$, and series the image of that of $t_0$ under the reduction of $y_0$) and $\psi':=y_0\circ(O\to\bar O)$, three witnesses are given: `hOD'`, that the series of $t_0\otimes_{y_0}S$ is an $\mathcal O_D$-homomorphism from the corresponding base change of $\Phi$ to $\overline{X^0_S}$; `hcb'`, that the degree-$0$ and degree-$1$ graded pieces of $(t_0\otimes_{y_0}S).\mathrm{XbarS}(g_S)$ for $j_{\bar S}(\iota,\psi',g_S)$ are complementary; and `hcΦg'`, the same complementarity for the base change of $\Phi$ over $S'/pS'$.
--
--   **Conclusion.** Let $D'$ be the graded Cartier module data of $\bigl((t_0\otimes_{y_0}S).\mathrm{XbarS}\,g_S\bigr)$ with structure map $j_{\bar S}(\iota,\psi',g_S)$ and complementarity witness `hcb'`, let $r'$ be `Rigidified.rigidNum` $\iota\ hc\Phi\ r_\Phi$ taken for $\psi'$, the datum $t_0\otimes_{y_0}S$, and the witnesses `hOD'`, $g_S$, `hcb'`, `hcΦg'`, and let $\beta:M(X)\to D'.M$ be the composite base change of Cartier modules along $f_0$, then $y_0$, then $S\to S/pS$, then the reduction of $g_S$. Then for every $i\in\{0,1\}$,
--   $$p^{a}\cdot r'(e_i)=p^{a+m}\cdot c'_i,$$
--   with $c'_0=D'.\mathrm{nMk}\bigl(\beta(\gamma_0),0\bigr)$ and $c'_1=D'.\mathrm{nVarpi}\Bigl(D'.\mathrm{nMk}\bigl(\beta(\gamma_1),0\bigr)\Bigr)$; here $\mathrm{nMk}(x,0)$ is the class of $(x,0)$ in the quotient $N$-module and $\mathrm{nVarpi}$ is the $\varpi$-action on it. Thus the normalisation `hN` of the rigidification numerator on the standard basis, valid at the node point over $\bar O$, holds verbatim after an arbitrary base change $y_0$ read over $S'$ through $g_S$, with the same exponents $a$ and $a+m$ and with $\gamma_0,\gamma_1$ transported by $\beta$.
--
--   A functoriality (base-change) step in the Cartier-theoretic description of the Čerednik–Drinfeld uniformisation: it transports the normalisation of the rigidification numerator of the node isogeny from the node point over $W(k)/p$ to an arbitrary base ring. It is used by [`CerednikDrinfeld.FormalODModule.exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq`](thm.html#CerednikDrinfeld.FormalODModule.exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq) and its degree-one twin, which produce $\eta$-sections with prescribed tangent data, and by [`CerednikDrinfeld.FormalODModule.lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq`](thm.html#CerednikDrinfeld.FormalODModule.lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq), which identifies the lattice attached to the corresponding Cartier quadruple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.smul_rigidNum_map_node_single_eq_smul_baseChange_of_rigidNum_single_eq
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
    (S : Type) [CommRing S] (y₀ : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* S) {S' : Type} [CommRing S'] (gS : S →+* S')
    (hOD' : FormalODModule.IsODHom (Rigidified.Φbar (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀)) (Rigidified.Xbar ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀)) (Rigidified.ρ ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀)))
    (hcb' : Rigidified.IsGradedSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) gS)
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) :
    ∀ i : Fin 2,
      p ^ a • Rigidified.rigidNum ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) hOD' gS hcb' hcΦg' (Pi.single i 1) =
        p ^ (a + m) • (![((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nMk (baseChange (reduceMap gS) (baseChange (Ideal.Quotient.mk (pIdeal p S)) (baseChange y₀ (baseChange f₀ (γ 0)))), 0),
            ((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nVarpi (((((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) gS) hcb').nMk (baseChange (reduceMap gS) (baseChange (Ideal.Quotient.mk (pIdeal p S)) (baseChange y₀ (baseChange f₀ (γ 1)))), 0))] i) := by sorry
