-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/4f038863-31c5-58c8-850b-ef4bd5a0b650
-- title:
--   Existence of the base-change map on special graded Cartier modules
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{p^2}$ for [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), i.e. $W(\mathbb{F}_{p^2})$. Let $S$, $T$, $B'$ be commutative rings equipped with ring maps $j_S\colon\mathbb{Z}_{p^2}\to S$, $j_T\colon\mathbb{Z}_{p^2}\to T$, $j'\colon\mathbb{Z}_{p^2}\to B'$, and let $i\colon S\to T$ and $q\colon T\to B'$ be ring maps. Let $D_S$, $D_T$, $D'$ be graded Cartier module data over $S$, $T$, $B'$ respectively: each consists of a module $M$ over the Witt vectors of the base ring together with additive endomorphisms $F$ (Frobenius) and $V$ (Verschiebung), a linear endomorphism $\varpi$, and a pair of complementary submodules $M=\mathrm{piece}\,0\oplus\mathrm{piece}\,1$, subject to $F(wx)=\sigma(w)F x$, $w\,Vx=V(\sigma(w)x)$, $V(w\,Fx)=V(w)x$, $FV=p$, $\varpi V=V\varpi$, $\varpi F=F\varpi$, $\varpi^2=p$, and the requirement that $F$, $V$, $\varpi$ each shift the grading by $1$. Each of the three is assumed special, i.e. to admit a homogeneous $V$-basis ($\gamma_i\in\mathrm{piece}\,i$ with every $x$ uniquely of the form $\sum_i \tau(c_i)\gamma_i+Vy$ for $c\in B^2$, $y\in M$) and to be $V$-adically complete (for every sequence $(x_m)_{m\in\mathbb{N}}$ there is a unique $s$ with $s\in\sum_{m<N}V^m x_m+V^N M$ for all $N$). Let $g\colon M_S\to M_T$ and $k\colon M_S\to M'$ be additive maps which are base changes along $i$ and along $q\circ i$ respectively, meaning each is semilinear for the induced map on Witt vectors, commutes with $F$, $V$ and $\varpi$, preserves the two graded pieces, and carries some homogeneous $V$-basis of $M_S$ to a homogeneous $V$-basis of the target. Finally let $\gamma\colon\mathrm{Fin}\,2\to M_S$ be a homogeneous $V$-basis of $M_S$ whose image $(g(\gamma_i))_i$ is a homogeneous $V$-basis of $M_T$. The conclusion is that there exists an additive map $h\colon M_T\to M'$ satisfying $h(w\cdot x)=W(q)(w)\cdot h(x)$ for all $w\in W(T)$ and $x\in M_T$, $h(Vx)=V(h(x))$ for all $x$, and $h(g(\gamma_i))=k(\gamma_i)$ for $i=0,1$. Only semilinearity, compatibility with $V$ and the values on the basis are asserted of $h$; compatibility with $F$ and $\varpi$ and preservation of the grading are not part of this conclusion.
--
--   This is the existence half of the universal property identifying a special graded Cartier module receiving a base change from $M_S$ with the $V$-adically completed base change $W(T)\,\widehat{\otimes}_{W(S)}M_S$, the map $h$ playing the role of $q\,\widehat{\otimes}\,k$. It is used by [`CerednikDrinfeld.GradedCartierModuleData.exists_baseChange_comp_eq_and_unique`](thm.html#CerednikDrinfeld.GradedCartierModuleData.exists_baseChange_comp_eq_and_unique), which adds the uniqueness statement and the factorisation of $k$ through $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange
    (p : ℕ) [Fact p.Prime] {S T B' : Type} [CommRing S] [CommRing T] [CommRing B']
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (i : S →+* T) (q : T →+* B')
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (g : DS.M →+ DT.M) (hg : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' i DS DT g)
    (k : DS.M →+ D'.M) (hk : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' (q.comp i) DS D' k)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ) (hgγ : DT.IsHomogeneousVBasis (fun i => g (γ i))) :
    ∃ h : DT.M →+ D'.M,
      (∀ (w : WittVector p T) (x : DT.M), h (w • x) = WittVector.map q w • h x) ∧
      (∀ x : DT.M, h (DT.verschiebung x) = D'.verschiebung (h x)) ∧
      ∀ i : Fin 2, h (g (γ i)) = k (γ i) := by sorry
