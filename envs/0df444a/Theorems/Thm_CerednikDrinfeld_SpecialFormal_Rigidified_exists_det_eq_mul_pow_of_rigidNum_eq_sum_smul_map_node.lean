-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/bf8fdfb8-699c-5f5b-b371-7ea0059561cc
-- title:
--   Node determinant det A = u p^{2m} for rigidified data
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, put $W=\mathrm{W}(k)$ and let $\iota\colon \mathrm{W}(\mathbb F_{p^2})\to W$ be a ring homomorphism, with reduction $\bar\jmath=\mathrm{pr}\circ\iota\colon \mathrm{W}(\mathbb F_{p^2})\to W/pW$. Let $\Phi$ be a formal $\mathcal O_D$-module over $W/pW$ (a two-dimensional commutative formal group with an action of $\mathrm{W}(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$, $\varpi\circ[a]=[\sigma a]\circ\varpi$) such that: $\Phi$ is special for $\bar\jmath$, i.e. the $\bar\jmath$-weight-$0$ and weight-$1$ parts of $\mathrm{Lie}\,\Phi$ are complementary and both invertible; $[p]$ has kernel of degree $p^4$; the weight-$0$ part of $\mathrm{Lie}\,\Phi$ lies in the kernel of the linear part of $\varpi$ on $\mathrm{Lie}\,\Phi$; and the two graded pieces of the Cartier module of $\Phi$ in degrees $0$ and $1$ (the eigenspaces where the Teichmüller action of $c\in\mathbb F_{p^2}$ is homothety by $\bar\jmath(\tau c)^{p^n}$) are complementary, as recorded by `hc\Phi`. Let $r_\Phi\colon \mathbb Z_p^2\to$ `NMod` of the graded Cartier module data of $\Phi$ be additive and such that for every canonical $L$-map $L$ it carries all of $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\eta(L)\cap N_0$. Let $g\in \mathrm{GL}_2(\mathbb Q_p)$ be the diagonal matrix $\mathrm{diag}(p,1)$. Over the edge chart ring $E=$ `EdgeFamily.edgeRingCharP p (W/pW)` let $X$ be a formal $\mathcal O_D$-module with $\gamma_0,\gamma_1$ a homogeneous $V$-basis of its Cartier module for the structure map of $\iota$ (each $\gamma_i$ in the graded piece of degree $i$, with invertible tangent matrix), whose $\varpi$-structure constants are the edge constants $\mathrm{edgeConstants}(p,\xi,\eta)$ of $E$, with $X$ special and $[p]$ of kernel degree $p^4$. Let $f_0\colon E\to W/pW$ be a ring homomorphism retracting the structural algebra map and killing $\xi$ and $\eta$. Let $m\in\mathbb N$ and $\rho_0$ a $2$-tuple of power series over $W/pW$ which is an $\mathcal O_D$-isogeny $\Phi\to X\otimes_{f_0}(W/pW)$ with kernel of degree $p^{4m}$; form the rigidified datum $t$ consisting of $X\otimes_{f_0}(W/pW)$, the integer $m$ and the reduction of $\rho_0$, and assume that $\rho$ of $t$ is an $\mathcal O_D$-homomorphism from $\bar\Phi$ to $\bar X$, and that the degree-$0$ and degree-$1$ graded pieces are complementary both for $\bar X$ of $t$ along the identity (`hcb`) and for $\bar\Phi$ along the identity (`hc\Phi g`). Finally let $c\colon\mathbb Z_p\to \mathrm{W}((W/pW)/p)$ be a ring homomorphism, $a\in\mathbb N$, and $A$ a $2\times 2$ matrix over $\mathbb Z_p$ such that for every $w\in\mathbb Z_p^2$, $p^a$ times the value at $w$ of the rigid numerator $\mathrm{rigidNum}$ (the composite of $r_\Phi$ with the $N$-module maps induced by base change $\Phi\to\bar\Phi$ and by $\bar\rho$) equals $p^a\sum_{j} c((Aw)_j)\cdot b_j$, where $b_0$ is the class $\mathrm{nMk}(\gamma_0,0)$ and $b_1=\mathrm{nVarpi}\,\mathrm{nMk}(\gamma_1,0)$, the $\gamma_i$ being transported along $f_0$ and the successive reductions mod $p$. Then there is a unit $u\in\mathbb Z_p^\times$ with $\det A=u\,p^{2m}$.
--
--   This is the rigidified, node-chart form of the determinant computation in the Čerednik–Drinfeld uniformisation theory of Boutot–Carayol: the matrix of the rigid numerator on the distinguished $\mathbb Z_p$-basis $(\gamma_0,\varpi\gamma_1)$ of the degree-$0$ $\eta$-piece at the node has determinant a unit times $p^{2m}$, where $4m$ is the height of the chosen isogeny. It feeds the construction of isogenies with prescribed lattice behaviour in [`CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq`](thm.html#CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq), the bridge from the field-level determinant statement to the edge-family setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
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
    (c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (a : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ w : Fin 2 → ℤ_[p],
      p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) w =
        p ^ a • ∑ j : Fin 2, c (A.mulVec w j) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
                ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] j)) :
    ∃ u : ℤ_[p]ˣ, A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * m) := by sorry
