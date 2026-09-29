-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
-- name    : CerednikDrinfeld.FormalODModule.exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/970b55d4-e13d-5e64-8a75-9830e10ed871
-- title:
--   Isogeny matrix on degree-zero Cartier pieces has determinant u p^h
-- statement:
--   Let $p$ be prime and $K$ a perfect field of characteristic $p$, and let $j$ be a ring homomorphism from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $K$. Let $Y, Z$ be formal $\mathcal{O}_D$-modules over $K$ in the sense of the project's structure `FormalODModule`, i.e. two-dimensional commutative formal group laws equipped with an action of $\mathbb{Z}_{p^2}$ and a uniformiser endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Assume each of $Y, Z$ is special for $j$ (the degree-$0$ and degree-$1$ parts of the Lie algebra are complementary and invertible) and has height $4$ in the sense that $[p]$ has kernel of degree $p^4$, and assume for each of $Y, Z$ that the degree-$0$ and degree-$1$ graded pieces of its Cartier module are complementary, where the degree-$n$ piece consists of those elements on which the induced action of the Teichmüller lift of any $c \in \mathbb{F}_{p^2}$ agrees with homothety by $j(\tau(c))^{p^n}$. Let $\rho$ be a pair of power series which is an $\mathcal{O}_D$-homomorphism $Y \to Z$ whose kernel has degree $p^{2h}$, let $c : \mathbb{Z}_p \to W(K)$ be a ring homomorphism, and let $e_0,e_1$ (resp. $e'_0,e'_1$) lie in the degree-$0$ graded piece of the Cartier module of $Y$ (resp. $Z$) and be such that every element of that piece is uniquely a $W(K)$-combination of them. Finally let $A \in M_2(\mathbb{Z}_p)$ satisfy $\rho_*(e_r) = \sum_s c(A_{sr})\,e'_s$, where $\rho_*$ is the $W(K)$-linear map on Cartier modules induced by $\rho$. Then there is a unit $u \in \mathbb{Z}_p^{\times}$ with $\det A = u\,p^{h}$.
--
--   This is the determinant–index computation for an isogeny of special formal $\mathcal{O}_D$-modules of height $4$: an isogeny of height $2h$ induces, on the degree-$0$ graded pieces of the Cartier modules, a map whose matrix over $\mathbb{Z}_p$ has determinant of valuation exactly $h$. It is used in the rigidification step of the Čerednik–Drinfeld uniformisation, where it feeds the statement [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y Z : FormalODModule p K) (hY : Y.IsSpecial j) (hZ : Z.IsSpecial j)
    (hY4 : Y.HasHeight 4) (hZ4 : Z.HasHeight 4)
    (hcY : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (hcZ : IsCompl (Z.gradedPiece j 0) (Z.gradedPiece j 1))
    (ρ : SpecialFormal.Series K) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ (2 * h))
    (c : ℤ_[p] →+* WittVector p K)
    (e : Fin 2 → MvFormalGroup.CartierModule p Y.F)
    (he : ∀ m ∈ Y.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r)
    (he0 : ∀ r, e r ∈ Y.gradedPiece j 0)
    (e' : Fin 2 → MvFormalGroup.CartierModule p Z.F)
    (he' : ∀ m ∈ Z.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e' r)
    (he'0 : ∀ r, e' r ∈ Z.gradedPiece j 0)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ r, MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom (e r) = ∑ s, c (A s r) • e' s) :
    ∃ u : ℤ_[p]ˣ, A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h := by sorry
