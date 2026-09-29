-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis
-- name    : CerednikDrinfeld.GradedCartierModuleData.baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/d118067c-0533-5a15-b582-5c7ed8dad1a9
-- title:
--   A recognition criterion for base changes of special graded Cartier modules
-- statement:
--   Let $p$ be a prime, let $T$ and $B'$ be commutative rings equipped with ring homomorphisms $j_T \colon W(\mathbb{F}_{p^2}) \to T$ and $j' \colon W(\mathbb{F}_{p^2}) \to B'$ (here `Zp2 p` is $W(\mathbb{F}_{p^2})$, the Witt vectors of the field with $p^2$ elements), and let $q \colon T \to B'$ be a ring homomorphism. Let $D_T$ be a graded Cartier module datum over $(T, j_T)$ and $D'$ one over $(B', j')$: each consists of a module $M$ over the Witt vectors of the base, additive endomorphisms $F$ and $V$, a linear endomorphism $\Pi$ (`varpi`), and two submodules $M_0, M_1$ forming a complementary pair, subject to the usual semilinearity and Cartier relations ($F(w\cdot x) = \sigma(w)\cdot F x$, $w \cdot Vx = V(\sigma(w)x)$, $V(w \cdot Fx) = (Vw)\cdot x$, $FV = p$, $\Pi V = V\Pi$, $\Pi F = F\Pi$, $\Pi^2 = p$), with $F$, $V$, $\Pi$ shifting the grading by one. Assume both data are special, i.e. each admits a homogeneous $V$-basis — a pair $\gamma_i \in M_i$ such that every $x$ is uniquely of the form $\sum_i \tau(c_i)\gamma_i + Vy$ with $c \in B^2$ and $y \in M$, where $\tau$ is the Teichmüller lift — and each is $V$-adically complete in the sense that every sequence $(x_m)$ has a unique sum $s$ with $s = \sum_{m<N} V^m x_m + V^N t$ for some $t$, for all $N$. Let $h \colon M_T \to M'$ be additive, semilinear along $W(q)$ (so $h(w\cdot x) = W(q)(w)\cdot h(x)$), and compatible with $V$. Let $\beta$ be a homogeneous $V$-basis of $D_T$ such that $(h(\beta_i))_i$ is a homogeneous $V$-basis of $D'$ and $h(\Pi \beta_i) = \Pi\, h(\beta_i)$ for $i = 0, 1$. Then $h$ satisfies `IsBaseChangeAlong' q DT D' h`: it is $W(q)$-semilinear, commutes with $F$, with $V$ and with $\Pi$, carries $M_{T,i}$ into $M'_i$ for $i = 0, 1$, and there is a homogeneous $V$-basis of $D_T$ whose image under $h$ is a homogeneous $V$-basis of $D'$.
--
--   This is the recognition criterion identifying a map of special graded Cartier modules as a scalar extension along a ring homomorphism: only semilinearity, compatibility with $V$, and compatibility with $\Pi$ on one homogeneous $V$-basis whose image is again such a basis need be checked. It feeds the construction and uniqueness of base-change maps (`exists_baseChange_comp_eq_and_unique`) in the Cartier-module description of special formal $\mathcal{O}_D$-modules used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {T B' : Type} [CommRing T] [CommRing B']
    {jT : CerednikDrinfeld.Zp2 p →+* T} {j' : CerednikDrinfeld.Zp2 p →+* B'} (q : T →+* B')
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (h : DT.M →+ D'.M)
    (hsl : ∀ (w : WittVector p T) (x : DT.M), h (w • x) = WittVector.map q w • h x)
    (hV : ∀ x : DT.M, h (DT.verschiebung x) = D'.verschiebung (h x))
    (β : Fin 2 → DT.M) (hβ : DT.IsHomogeneousVBasis β) (hβ' : D'.IsHomogeneousVBasis (fun i => h (β i)))
    (hvarpi : ∀ i : Fin 2, h (DT.varpi (β i)) = D'.varpi (h (β i))) :
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DT D' h := by sorry
