-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isODHom_and_isGradedSbar_and_isGradedPhiS_map_node
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isODHom_and_isGradedSbar_and_isGradedPhiS_map_node
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/f0e816bb-c566-5f4d-9f1c-4093bbf19beb
-- title:
--   Node witnesses: mathcal O_D-linearity and graded reductions
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon \mathbb{W}(p,\mathbb{F}_{p^2})\to W(k)$, and put $j=\mathrm{mk}\circ\iota$ where $\mathrm{mk}\colon W(k)\to W(k)/(p)$ is the quotient map. Let $\Phi$ be a formal $\mathcal O_D$-module of dimension $2$ over $W(k)/(p)$ which is special for $j$ (its zero and one Lie eigenspaces are complementary and invertible), has height $4$, satisfies $\Phi.\mathrm{lieZero}\,j\subseteq\ker\Phi.\mathrm{lieVarpi}$, and whose Cartier graded pieces of weights $0$ and $1$ for $j$ are complementary, say by `hcΦ`; let $r_\Phi\colon \mathbb{Z}_p^2\to$ `NMod` of the associated `GradedCartierModuleData` be an additive map which, for every canonical $L$-map $L$, restricts to a bijection of the whole of $\mathbb{Z}_p^2$ onto the weight-$0$ $\eta$-piece of $L$. Let $g\in GL_2(\mathbb{Q}_p)$ be $\mathrm{diag}(p,1)$. Let $X$ be a formal $\mathcal O_D$-module over the edge chart ring $E=$ `EdgeFamily.edgeRingCharP p (W(k)/(p))` carrying a homogeneous $V$-basis $\gamma$ for the structure map $\iota$ followed by $W(k)/(p)\to E$, with structure constants the edge constants of $E$, special for that structure map and of height $4$; let $f_0\colon E\to W(k)/(p)$ be a ring homomorphism retracting $W(k)/(p)\to E$ and killing $\xi$ and $\eta$; let $m\in\mathbb{N}$ and let $\rho_0$ be a pair of power series which is an $\mathcal O_D$-isogeny $\Phi\to X\otimes_{f_0}W(k)/(p)$ of height $4m$. Writing $t^0$ for the rigidified triple consisting of $X\otimes_{f_0}W(k)/(p)$, the integer $m$ and the reduction $\bar\rho_0$ of $\rho_0$ modulo $p$, the conclusion is the conjunction of three statements: (i) $\bar\rho_0$ is an $\mathcal O_D$-homomorphism from the reduction of $\Phi$ to the reduction of $X\otimes_{f_0}W(k)/(p)$, that is, it is a homomorphism of formal group laws commuting with all the $\mathbb{W}(p,\mathbb{F}_{p^2})$-actions and with $\varpi$; (ii) for the identity base change of $W(k)/(p)$, the weight-$0$ and weight-$1$ Cartier graded pieces of the reduction of $t^0.X$, taken with respect to the induced structure map, are complementary; (iii) the same complementarity for the reduction of $\Phi$ with respect to its induced structure map.
--
--   These are the three auxiliary inputs — $\mathcal O_D$-linearity of the reduced isogeny and gradedness of the two Cartier modules involved — required to feed a node triple into the rigidification machinery of the Čerednik–Drinfeld uniformisation. The statement is used by [`CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq`](thm.html#CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isODHom_and_isGradedSbar_and_isGradedPhiS_map_node.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isODHom_and_isGradedSbar_and_isGradedPhiS_map_node
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
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m)) :
    (FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))) ∧
    (Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) ∧
    (Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by sorry
