-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
-- name    : CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/095cff50-2e18-5c44-bac9-d66974dada86
-- title:
--   Cartier quadruples at geometric points of the edge family
-- statement:
--   Throughout, $p$ is a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring homomorphism (the type `Zp2 p` is $W(\mathbb F_{p^2})$). For a commutative ring $B$, `pIdeal p B` is the ideal $(p)$, and a `FormalODModule p B` consists of a two‑dimensional commutative formal group law $F$ over $B$ together with an action of $W(\mathbb F_{p^2})$ by law endomorphisms and a law endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$. For such an object $X$ and a ring homomorphism $j : W(\mathbb F_{p^2})\to B$, `X.gradedPiece j n` is the subgroup of $f$ in the Cartier module of $F$ with $\operatorname{endAct}(X.\mathrm{actEnd}(\tau(c)))f = \mathrm{homothety}(j(\tau(c))^{p^{n}})f$ for all $c\in\mathbb F_{p^2}$ ($\tau$ the Teichmüller lift), `X.IsSpecial j` says that the Lie pieces `lieZero j` and `lieOne j` are complementary and each an invertible $B$‑module, and `X.HasHeight h` says that $X.\mathrm{act}(p)$ has kernel of degree $p^{h}$.
--
--   The module over the base point: $\Phi$ is a formal $\mathcal O_D$‑module over $W(k)/(p)$, with structure map $j_\Phi$ the composite of $\iota$ with the quotient map $W(k)\to W(k)/(p)$. The hypotheses on $\Phi$ are: `hΦ`, that $\Phi$ is special for $j_\Phi$; `hΦ4`, that $\Phi$ has height $4$; `h0Φ`, that $\Phi.\mathrm{lieZero}\,j_\Phi$ is contained in the kernel of $\Phi.\mathrm{lieVarpi}$ (the action on the Lie algebra of the linear part of $\varpi$); and `hcΦ`, that the graded pieces of $\Phi$ in degrees $0$ and $1$ are complementary. Via `hcΦ` one forms the graded Cartier module datum $D_\Phi = \Phi.\mathrm{toGradedCartierModuleData}\,j_\Phi\,\mathrm{hcΦ}$ (underlying module the Cartier module of $\Phi.F$, with Frobenius, the integral Verschiebung, the operator $\varpi$ and the two graded pieces). Further, $r_\Phi : (\mathrm{Fin}\,2\to\mathbb Z_p)\to D_\Phi.\mathrm{NMod}$ is an additive map, and `hrΦ` requires that for every additive $L : D_\Phi.M \to D_\Phi.\mathrm{NMod}$ which is a canonical $L$‑map (a Cartier $L$‑map admitting a lift along a surjection from a special graded Cartier module datum), $r_\Phi$ maps $(\mathrm{Fin}\,2\to\mathbb Z_p)$ bijectively onto the degree‑$0$ $\eta$‑piece `etaPiece L _ 0` of $D_\Phi$.
--
--   The matrix $g\in \mathrm{GL}_2(\mathbb Q_p)$ is subject to `hg`: $g = \operatorname{diag}(p,1)$.
--
--   The edge family: $E$ denotes `EdgeFamily.edgeRingCharP p (W(k)/(p))`, that is `FormalOmega.chartERing (W(k)/(p)) 0 p`, a $W(k)/(p)$‑algebra with distinguished elements $\xi$ and $\eta$. Over $E$ there is a formal $\mathcal O_D$‑module $X$ and a pair $\gamma = (\gamma_0,\gamma_1)$ of elements of the Cartier module of $X.F$, with structure map $\iota$ followed by $W(k)\to W(k)/(p)\to E$. The hypotheses are: `hγ`, that $\gamma$ is a homogeneous $V$‑basis, i.e. $\gamma_i$ lies in the graded piece of degree $i$ and the determinant of the matrix of tangent vectors $(\mathrm{tangent}(\gamma_i)_k)$ is a unit; `hγa`, that $\gamma$ has structure constants `EdgeFamily.edgeRingConstants p (W(k)/(p))` $=$ `edgeConstants p ξ η`, meaning that for each $i$ and each $N$ the element $\varpi(\gamma_i)$ is congruent, modulo $V^{N}$ of the Cartier module, to $\sum_{m<N} V^{m}\big(\mathrm{homothety}(a_{m,i})\gamma_{\mathrm{piIndex}(m,i)}\big)$; `hXs`, that $X$ is special; and `hX4`, that $X$ has height $4$.
--
--   The node: $f_0 : E \to W(k)/(p)$ is a ring homomorphism with `hf₀` that $f_0$ is a retraction of the structure map $W(k)/(p)\to E$, and `hf₀ξ`, `hf₀η` that $f_0(\xi) = 0$ and $f_0(\eta) = 0$.
--
--   The isogeny from the base point: $m$ is a natural number and $\rho_0$ a pair of power series over $W(k)/(p)$ such that `hρ₀` holds: $\rho_0$ is an isogeny of height $4m$ from $\Phi$ to $X$ base‑changed along $f_0$, i.e. an $\mathcal O_D$‑homomorphism whose kernel has degree $p^{4m}$. Write $t_0$ for the rigidified object `Rigidified.mk (Φ := Φ) (X.map f₀) m` with series the reduction of $\rho_0$ along the quotient by $(p)$ in $W(k)/(p)$. The hypotheses on $t_0$ are: `hOD₀`, that the series of $t_0$ is an $\mathcal O_D$‑homomorphism from $t_0.\Phi\mathrm{bar}$ to $t_0.X\mathrm{bar}$; `hcb`, that the degree‑$0$ and degree‑$1$ graded pieces of `Rigidified.XbarS t₀ (RingHom.id _)` are complementary for the structure map `Rigidified.jSbar`; and `hcΦg`, the corresponding complementarity for `PhibarS` of $\Phi$. With these, `Rigidified.rigidNum` is the additive map $(\mathrm{Fin}\,2\to\mathbb Z_p)\to$ the $N$‑module of `XbarS t₀ (RingHom.id _)` obtained from $r_\Phi$ by base change and then by the map induced by the reduction of $\rho_0$. The normalisation hypothesis `hN` (with an auxiliary exponent $a\in\mathbb N$) states, for each $i\in\mathrm{Fin}\,2$, that $p^{a}$ times the value of `rigidNum` at the $i$‑th standard vector `Pi.single i 1` equals $p^{a+m}$ times the $i$‑th entry of the pair whose entries are: $\mathrm{nMk}(\bar\gamma_0,0)$ for $i=0$, and $\mathrm{nVarpi}\big(\mathrm{nMk}(\bar\gamma_1,0)\big)$ for $i=1$, where $\bar\gamma_j$ is $\gamma_j$ base‑changed along $f_0$, then along the quotient by $(p)$, then along `reduceMap (RingHom.id _)`.
--
--   The edge isogeny: $\rho_1$ is a morphism of formal $\mathcal O_D$‑modules from $X$ base‑changed along $f_0$ and then along $W(k)/(p)\to E$ to $X$ itself, satisfying `hρ₁0` and `hρ₁1`: the induced map on Cartier modules sends the base change of $\gamma_0$ to $p\,\gamma_0 - V\big(\tau(\eta^{p^{2}})\gamma_1\big)$ and the base change of $\gamma_1$ to $p\,\gamma_1 - V\big(\tau(\xi^{p^{2}})\gamma_0\big)$, where $V$ is the integral Verschiebung and $\tau$ the Teichmüller lift; and `hρ₁h`, that the series of $\rho_1$ is an isogeny of height $4$.
--
--   Conclusion. For every algebraically closed field $\Omega$ which is a $\mathbb Z_p$‑algebra and every ring homomorphism $y : E \to \Omega$, there exist a Drinfeld datum $Q$ over $\Omega$ and a Deligne datum $d$ over $\Omega$, both for $\mathcal O = \mathbb Z_p$, $K=\mathbb Q_p$ and uniformiser $p$, such that the following four assertions hold.
--
--   First, let $t$ be the rigidified object over $E$ with module $X$, integer $m+1$, and series the composite of the reduction of the series of $\rho_1$ modulo $(p)$ in $E$ with the image of $\rho_0$ under $W(k)/(p)\to E\to E/(p)$; let $t\otimes_y\Omega$ denote its base change along $y$ (module $X$ base‑changed along $y$, same integer, series transported by `reduceMap y`). Then $t\otimes_y\Omega$ satisfies `IsCartierQuadruple` with respect to $\iota$, `hcΦ`, $r_\Phi$, the structure map $W(k)\to W(k)/(p)\to E\to\Omega$ and the datum $Q$: the series of $t\otimes_y\Omega$ is an $\mathcal O_D$‑homomorphism from $\Phi\mathrm{bar}$ to $X\mathrm{bar}$, and there are $\Omega$‑linear isomorphisms of the invertible modules $Q.T_0$, $Q.T_1$ onto the Lie pieces `lieZero` and `lieOne` of the module of $t\otimes_y\Omega$ which intertwine $Q.\Pi_0$ and $Q.\Pi_1$ with `lieVarpi`, while at each point $x$ of $\operatorname{Spec}\Omega$ membership of a vector in $Q.N_0\,x$ (respectively $Q.N_1\,x$) is equivalent to the existence, over some localisation away from a function not in $x$ and for some canonical $L$‑map, of an $\eta$‑section of degree $0$ (respectively $1$) representing it, these sections being compatible with the structure maps $Q.u_0$ and $Q.u_1$ into the stalks of $Q.T_0$ and $Q.T_1$.
--
--   Second, `Q.IsQuadrupleOf d`: for every point $x$ of $\operatorname{Spec}\Omega$, the datum $d$ is edge‑nondegenerate at $x$ for the pair of lattices $Q.L_0\,x \le Q.L_1\,x$, and the kernels of $Q.u_0\,x$ and $Q.u_1\,x$ are the lines attached by $d$, transported to the local ring, to $Q.L_0\,x$ and $Q.L_1\,x$ respectively.
--
--   Third, at the standard full lattice $\mathbb Z_p^2\subset\mathbb Q_p^2$ the line of $d$ is the $\Omega$‑span of the single element
--   $$y(\xi)\otimes_{\mathbb Z_p} e_0 + 1\otimes_{\mathbb Z_p} e_1$$
--   of the base change $\Omega\otimes_{\mathbb Z_p}\mathbb Z_p^2$, where $e_0,e_1$ are the standard basis vectors.
--
--   Fourth, at the lattice $g\cdot\mathbb Z_p^{2}$ obtained by the action of $g$ the line of $d$ is the image, under the base‑changed isomorphism `actBaseChange Ω g (stdFullLattice ℚ_[p])`, of the $\Omega$‑span of $1\otimes_{\mathbb Z_p} e_0 + y(\eta)\otimes_{\mathbb Z_p} e_1$.
--
--   This is the geometric‑fibre statement for the rigidified family over the standard edge chart in the Čerednik–Drinfeld description of the $p$‑adic uniformisation: at every geometric point of the edge ring the Cartier quadruple of the rigidified formal $\mathcal O_D$‑module is the Drinfeld quadruple of a Deligne datum whose lines at the two vertices $\mathbb Z_p^2$ and $\operatorname{diag}(p,1)\mathbb Z_p^2$ are given explicitly by the images of the chart coordinates $\xi$ and $\eta$. It is obtained by combining the three cases $y(\xi)\neq 0$, $y(\xi)=0\neq y(\eta)$ and $y(\xi)=y(\eta)=0$, and it feeds the construction of admissible families over the whole edge family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny.lean

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

theorem CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
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
(ρ₁ : FormalODModule.Hom ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X)
(hρ₁0 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))
(hρ₁1 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))
(hρ₁h : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁.toSeries 4)
    :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* Ω),
      ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
        ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q ∧
        Q.IsQuadrupleOf d ∧
        d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap := by sorry
