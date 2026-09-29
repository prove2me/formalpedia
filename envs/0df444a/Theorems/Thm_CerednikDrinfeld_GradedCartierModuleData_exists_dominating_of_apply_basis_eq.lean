-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_dominating_of_apply_basis_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f5ce5b96-c188-5cec-bbfb-9e1f3e9e5f88
-- title:
--   Matched lifts of a special Cartier module admit a common domination
-- statement:
--   Let $p$ be a prime, let $B$, $S_1$, $S_2$ be commutative rings, and let $j : \mathbb{W}(\mathbb{F}_{p^2}) \to B$, $j_1 : \mathbb{W}(\mathbb{F}_{p^2}) \to S_1$, $j_2 : \mathbb{W}(\mathbb{F}_{p^2}) \to S_2$ be ring maps (the source being `Zp2 p`, the Witt vectors of $\mathbb{F}_{p^2}$), together with ring maps $q_1 : S_1 \to B$, $q_2 : S_2 \to B$ satisfying $q_1 \circ j_1 = j$ and $q_2 \circ j_2 = j$, and with $S_1$, $S_2$ free of $p$-torsion in the sense that $ps = 0$ forces $s = 0$. Let $D$ be graded Cartier module data over $(B,j)$ — that is, a module $M$ over $\mathbb{W}(B)$ equipped with additive maps $F$, $V$, a $\mathbb{W}(B)$-linear $\varpi$ and a pair of complementary submodules `piece 0`, `piece 1` shifted by one by each of $F$, $V$, $\varpi$, subject to the usual Cartier relations $F(wx) = \sigma(w)F(x)$, $wV(x) = V(\sigma(w)x)$, $V(wF(x)) = V(w)x$, $F(V(x)) = px$, $\varpi V = V\varpi$, $\varpi F = F\varpi$, $\varpi^2 = p$ — and let $D_1$, $D_2$ be such data over $(S_1,j_1)$, $(S_2,j_2)$; assume each of $D$, $D_1$, $D_2$ is special, i.e. possesses a homogeneous $V$-basis (a pair $\gamma_0 \in$ `piece 0`, $\gamma_1 \in$ `piece 1` such that every element is uniquely $\sum_i \tau(c_i)\gamma_i + V(y)$ with $c_i$ in the base ring, $\tau$ the Teichmüller lift) and is $V$-adically complete. Let $f_1 : D_1.M \to D.M$ and $f_2 : D_2.M \to D.M$ be additive maps that are base changes along $q_1$, respectively $q_2$: each is semilinear for $\mathbb{W}(q_i)$, commutes with $F$, $V$ and $\varpi$, preserves the grading, and carries some homogeneous $V$-basis of the source to a homogeneous $V$-basis of $D$. Finally let $\gamma_1$, $\gamma_2$ be homogeneous $V$-bases of $D_1$, $D_2$ with $f_1(\gamma_1 i) = f_2(\gamma_2 i)$ for $i \in \{0,1\}$. The conclusion asserts the existence of a commutative ring $S_3$ with a ring map $j_3$ from $\mathbb{W}(\mathbb{F}_{p^2})$, ring maps $r_1 : S_3 \to S_1$ and $r_2 : S_3 \to S_2$ with $r_1 \circ j_3 = j_1$, $r_2 \circ j_3 = j_2$ and $q_1 \circ r_1 = q_2 \circ r_2$, with $S_3$ again free of $p$-torsion, of special graded Cartier module data $D_3$ over $(S_3,j_3)$ with a homogeneous $V$-basis $\gamma_3$, and of additive maps $g_1 : D_3.M \to D_1.M$, $g_2 : D_3.M \to D_2.M$ which are base changes along $r_1$, $r_2$ respectively, satisfy $g_1(\gamma_3 i) = \gamma_1 i$ and $g_2(\gamma_3 i) = \gamma_2 i$ for both $i$, and satisfy $f_1(g_1(x)) = f_2(g_2(x))$ for all $x$ in $D_3.M$.
--
--   This is the gluing step in the proof that the lift attached to a special formal module is independent of the chosen $p$-torsion-free lift of the base, as in Boutot–Carayol's treatment of the Čerednik–Drinfel'd uniformisation: two lifts with matching images of their $V$-bases are dominated by a third, realised by the fibre products $S_1 \times_B S_2$ and $D_1.M \times_{D.M} D_2.M$. It is used by the results on canonical $L$-maps, `IsCanonicalLMap.apply_comp_eq_nMap_apply_of_torsionFree` and `IsCanonicalLMap.eq_of_isNilpotent`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_dominating_of_apply_basis_eq
    (p : ℕ) [Fact p.Prime] {B S₁ S₂ : Type} [CommRing B] [CommRing S₁] [CommRing S₂]
    (j : CerednikDrinfeld.Zp2 p →+* B)
    (j₁ : CerednikDrinfeld.Zp2 p →+* S₁) (j₂ : CerednikDrinfeld.Zp2 p →+* S₂)
    (q₁ : S₁ →+* B) (q₂ : S₂ →+* B) (hq₁ : q₁.comp j₁ = j) (hq₂ : q₂.comp j₂ = j)
    (hS₁ : ∀ s : S₁, (p : S₁) * s = 0 → s = 0) (hS₂ : ∀ s : S₂, (p : S₂) * s = 0 → s = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D₁ : CerednikDrinfeld.GradedCartierModuleData p S₁ j₁) (hD₁ : D₁.IsSpecialCartierModule)
    (D₂ : CerednikDrinfeld.GradedCartierModuleData p S₂ j₂) (hD₂ : D₂.IsSpecialCartierModule)
    (f₁ : D₁.M →+ D.M) (hf₁ : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q₁ D₁ D f₁)
    (f₂ : D₂.M →+ D.M) (hf₂ : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q₂ D₂ D f₂)
    (γ₁ : Fin 2 → D₁.M) (hγ₁ : D₁.IsHomogeneousVBasis γ₁)
    (γ₂ : Fin 2 → D₂.M) (hγ₂ : D₂.IsHomogeneousVBasis γ₂)
    (hγ : ∀ i : Fin 2, f₁ (γ₁ i) = f₂ (γ₂ i)) :
    ∃ (S₃ : Type) (_ : CommRing S₃) (j₃ : CerednikDrinfeld.Zp2 p →+* S₃) (r₁ : S₃ →+* S₁) (r₂ : S₃ →+* S₂)
      (_ : r₁.comp j₃ = j₁) (_ : r₂.comp j₃ = j₂) (_ : q₁.comp r₁ = q₂.comp r₂)
      (_ : ∀ s : S₃, (p : S₃) * s = 0 → s = 0)
      (D₃ : CerednikDrinfeld.GradedCartierModuleData p S₃ j₃) (_ : D₃.IsSpecialCartierModule)
      (γ₃ : Fin 2 → D₃.M) (_ : D₃.IsHomogeneousVBasis γ₃)
      (g₁ : D₃.M →+ D₁.M) (g₂ : D₃.M →+ D₂.M),
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' r₁ D₃ D₁ g₁ ∧
        CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' r₂ D₃ D₂ g₂ ∧
        (∀ i : Fin 2, g₁ (γ₃ i) = γ₁ i) ∧ (∀ i : Fin 2, g₂ (γ₃ i) = γ₂ i) ∧
        ∀ x : D₃.M, f₁ (g₁ x) = f₂ (g₂ x) := by sorry
