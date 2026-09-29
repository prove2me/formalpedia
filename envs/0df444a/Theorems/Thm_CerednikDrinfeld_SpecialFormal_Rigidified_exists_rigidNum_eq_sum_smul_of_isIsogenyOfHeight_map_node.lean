-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/df2a80a4-78ce-575e-b0de-72dd210e26d1
-- title:
--   Integral p-adic matrix for the rigidification numerator at a node
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : \mathrm{Zp2}\,p = W(\mathbb{F}_{p^2}) \to W(k)$ a ring homomorphism, with $\bar\jmath$ the induced map to $W(k)/p$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/p$ which is special for $\bar\jmath$ (its $\bar\jmath$-eigencomponents $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of the Lie module are complementary and invertible), has height $4$ in the sense that multiplication by $p$ has kernel of degree $p^4$, and satisfies $\mathrm{lieZero} \le \ker(\mathrm{lieVarpi})$; assume the graded pieces of index $0$ and $1$ of its Cartier module are complementary, as witnessed by $h c_\Phi$, and let $r_\Phi : \mathbb{Z}_p^2 \to \mathrm{NMod}$ of the associated graded Cartier module data be an additive map which, for every canonical $L$-map $L$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ piece $\mathrm{etaPiece}\,L\,0$. Let $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ be equal to $\mathrm{diag}(p,1)$. Let $X$ be a formal $\mathcal{O}_D$-module over the edge ring $\mathrm{edgeRingCharP}\,p\,(W(k)/p)$ carrying a homogeneous $V$-basis $\gamma = (\gamma_0,\gamma_1)$ for the structure map built from $\iota$, with structure constants the edge constants attached to $\xi,\eta$, special and of height $4$. Let $f_0$ be a ring map from the edge ring to $W(k)/p$ splitting the structural algebra map and sending $\xi$ and $\eta$ to $0$ (a node point), let $m \in \mathbb{N}$ and let $\rho_0$ be a $2$-tuple of power series which is an $\mathcal{O}_D$-isogeny $\Phi \to X \otimes_{f_0} (W(k)/p)$ with kernel of degree $p^{4m}$. Form the rigidified datum $t = (X\otimes_{f_0}(W(k)/p),\, m,\, \bar\rho_0)$, assume its $\rho$ is an $\mathcal{O}_D$-homomorphism from $t.\Phi\mathrm{bar}$ to $t.X\mathrm{bar}$, and assume the two gradedness conditions $\mathrm{IsGradedSbar}$ and $\mathrm{IsGradedPhiS}$ for the identity map of $W(k)/p$. Finally let $c : \mathbb{Z}_p \to W\big((W(k)/p)/p\big)$ be a ring homomorphism. Then there exist $a \in \mathbb{N}$ and a matrix $A \in M_2(\mathbb{Z}_p)$ such that for every $w \in \mathbb{Z}_p^2$ one has $p^a \cdot \mathrm{rigidNum}(\dots)(w) = p^a \cdot \sum_{j} c\big((Aw)_j\big) \cdot b_j$, where $\mathrm{rigidNum}$ is the composite of $r_\Phi$ with the maps on graded $N$-modules induced by base change along $f_0$ and reduction and by push-forward along $\rho$, and where $b_0 = \mathrm{nMk}(\bar\gamma_0, 0)$ and $b_1 = \mathrm{nVarpi}\,\mathrm{nMk}(\bar\gamma_1, 0)$ for $\bar\gamma_i$ the successive base changes of $\gamma_i$ along $f_0$, the quotient by $p$ and the induced reduction map.
--
--   This is the integrality step in the Čerednik–Drinfeld strand: at a node of the edge family, the numerator of a rigidification of a special formal $\mathcal{O}_D$-module of height $4$ is expressed, after clearing a bounded power of $p$, by a matrix with entries in $\mathbb{Z}_p$ relative to the distinguished pair of generators of the degree-$0$ $\eta$-piece. It is used by [`CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq`](thm.html#CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node
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
    (c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) :
    ∃ (a : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]), ∀ w : Fin 2 → ℤ_[p],
      p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) w =
        p ^ a • ∑ j : Fin 2, c (A.mulVec w j) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
                ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] j) := by sorry
