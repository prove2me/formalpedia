-- Prove2me | Theorems.Thm_CerednikDrinfeld_CartierLift_exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt
-- name    : CerednikDrinfeld.CartierLift.exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/76121776-b5e0-539e-b1bd-5c3e9a5c6ff7
-- title:
--   Universal digits forcing the relation p fᵢ=[p]fᵢ+sum_k V^k(d_{k,i}f)
-- statement:
--   Let $p$ be a prime and let $U$ denote the ring [`CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) (0,0) (0,1)`](def/CerednikDrinfeld_CartierStructureConstants.html#L180), i.e. the polynomial ring over $W(\mathbb F_{p^2})=$ `Zp2 p` in variables $X_{m,i}$ indexed by $(m,i)\in\mathbb N\times\mathbb F_2$ modulo the single relation $X_{0,0}X_{0,1}-p$, with $X_b$ denoting `liftVar` of $b$. The assertion is that there is a family $C_{m,i,l}\in U$ ($m\in\mathbb N$, $i,l\in\mathbb{Z}/2$) with two properties. First, $C_{m,i,l}=0$ unless $l\equiv m+i+1 \pmod 2$, that is unless $l=$ `piIndex m i`. Second, for every $2$-dimensional commutative formal group law $\Phi$ over $U$ (a pair of power series in two sets of two variables with vanishing constant term, identity linear part, associative and commutative), every $f:\mathbb{Z}/2\to$ `CartierModule p Φ` whose tangent vectors are the standard basis, $\mathrm{tangent}(f_i)_l=\delta_{il}$, and every $h:\mathbb N\to\mathbb{Z}/2\to$ `CartierModule p Φ` such that the Frobenius of each $f_i$ admits for every $N$ the expansion $F f_i=\sum_{m<N}V^m\bigl(\sum_l \langle C_{m,i,l}\rangle f_l\bigr)+V^N h_{N,i}$ (with $V=$ `verschiebungInt` and $\langle a\rangle=$ `homothety a`), one has, for all $N$ and $i$, some $s$ in the Cartier module with
--   $$p\, f_i=[p]\,f_i+\sum_{k<N}V^{k+1}\Bigl(\bigl(\textstyle\sum_{m<k+2}[\,X_{m,i}^{\,p^{k+1-m}}X_{k+1-m,\ \mathrm{piIndex}\,m\,i}\,]\bigr)\cdot f_{\mathrm{piIndex}\,k\,i}\Bigr)+V^{N+1}s,$$
--   where $p\,f_i$ is the $p$-fold sum, $[\,\cdot\,]$ is the Teichmüller map $U\to W(U)$ and the dots denote the $W(U)$-action on the Cartier module.
--
--   This is the finite-order (modulo $V^{N+1}$) form of the relation $\pi\gamma_i=[\pi]\gamma_i+\sum_{m\ge 1}V^m(d_{m,i}\gamma_{m+i})$ of Boutot–Carayol, expressing the $\Pi^2=p$ condition on the Cartier-module generators of a special formal $\mathcal O_D$-module in terms of its Teichmüller structure constants over the universal ring $U$. It is used in the construction of a homogeneous basis with structure constants given by the variables $X_{m,i}$, i.e. by `exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar`, within the Cerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CartierLift_exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.CartierLift.exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt
    (p : ℕ) [Fact p.Prime] :
    ∃ C : ℕ → Fin 2 → Fin 2 →
        CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1),
      (∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → C m i l = 0) ∧
      ∀ (Φ : MvFormalGroup 2
            (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)))
        [Φ.IsComm]
        (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
        (_hf : ∀ i l, MvFormalGroup.CartierModule.tangent (f i) l = if i = l then 1 else 0)
        (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
        (_hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
          (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
              (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (C m i l) (f l))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
        (N : ℕ) (i : Fin 2),
        ∃ s : MvFormalGroup.CartierModule p Φ,
          p • f i =
            WittVector.teichmuller p
                (p : CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)) •
              f i +
            (∑ k ∈ Finset.range N,
              (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
                ((∑ m ∈ Finset.range (k + 2),
                    WittVector.teichmuller p
                      (CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
                          ((0, 0) : ℕ × Fin 2) (0, 1) (m, i) ^ p ^ (k + 1 - m) *
                        CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
                          ((0, 0) : ℕ × Fin 2) (0, 1)
                          (k + 1 - m, CerednikDrinfeld.FormalODModule.piIndex m i))) •
                  f (CerednikDrinfeld.FormalODModule.piIndex k i))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s := by sorry
