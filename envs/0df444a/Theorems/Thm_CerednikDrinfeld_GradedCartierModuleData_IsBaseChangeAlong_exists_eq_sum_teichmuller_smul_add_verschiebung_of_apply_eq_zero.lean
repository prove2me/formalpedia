-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/2cdc936a-3149-5fbf-b00f-576a2b66988e
-- title:
--   Kernel of a graded Cartier base change to first V-order
-- statement:
--   Fix a prime $p$, commutative rings $S$ and $B$, a ring homomorphism $jS$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ (written `Zp2 p`) to $S$, and a ring homomorphism $\varphi \colon S \to B$. Let $Dl$ be graded Cartier module data over $S$ along $jS$ and $D$ graded Cartier module data over $B$ along $\varphi \circ jS$; each consists of a $W(p,\cdot)$-module $M$ with additive endomorphisms $F$, $V$, a linear $\varpi$, and a pair of complementary submodules `piece 0`, `piece 1`, satisfying the usual Cartier relations ($F$ is $\sigma$-semilinear, $w \cdot V x = V(F w \cdot x)$, $V(w \cdot F x) = V w \cdot x$, $F V = p$, $\varpi$ commutes with $F$ and $V$, $\varpi^2 = p$) and the grading shift by $1$ for $V$, $F$, $\varpi$. Let $f \colon Dl.M \to D.M$ be additive and a base change along $\varphi$: $f$ is semilinear for $W(\varphi)$, commutes with $F$, $V$ and $\varpi$, preserves the pieces, and some homogeneous $V$-basis of $Dl.M$ has $f$-image a homogeneous $V$-basis of $D.M$. Let $\gamma_0, \gamma_1$ be a homogeneous $V$-basis of $Dl.M$, i.e. $\gamma_i \in Dl.\mathrm{piece}\,i$ and every element of $Dl.M$ is uniquely of the form $\sum_i [c_i]\gamma_i + V y$ with $c \in S^2$, $y \in Dl.M$, and assume $(f(\gamma_0), f(\gamma_1))$ is likewise a homogeneous $V$-basis of $D.M$. Then for every $x$ with $f(x) = 0$ there are $c \colon \mathrm{Fin}\,2 \to S$ and $y \in Dl.M$ with $\varphi(c_i) = 0$ for both $i$, $f(y) = 0$, and $x = \sum_i [c_i]\gamma_i + V y$, where $[\,\cdot\,]$ denotes the Teichmüller lift `WittVector.teichmuller p`. Of the base-change hypothesis the proof uses only the $W(\varphi)$-semilinearity of $f$ and its commutation with $V$; no surjectivity of $\varphi$ and no completeness assumption occur.
--
--   This is the first-order description of the kernel of a base change of (graded) Cartier module data, as in Boutot–Carayol II (3.7): an element killed by $f$ has a $V$-expansion whose Teichmüller coefficients die in $B$ and whose $V$-tail is again in the kernel; iterating and passing to the limit gives the full statement $\ker f = \{\sum_m V^m \sum_i [a_{m,i}]\gamma_i : a_{m,i} \in \ker \varphi\}$. It is used in the Čerednik–Drinfel'd layer, for the vanishing statement `IsCartierLMap.nMap_apply_eq_zero_of_apply_eq_zero` and for the bijectivity criterion `bijective_eta_map_of_surjective_of_isNilpotent`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (γ : Fin 2 → Dl.M) (hγ : Dl.IsHomogeneousVBasis γ) (hγ' : D.IsHomogeneousVBasis (fun i => f (γ i)))
    (x : Dl.M) (hx : f x = 0) :
    ∃ (c : Fin 2 → S) (y : Dl.M), (∀ i, φ (c i) = 0) ∧ f y = 0 ∧
      x = (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + Dl.verschiebung y := by sorry
