-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_baseChange_comp_eq_and_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f19a8f90-d0a4-5553-9cfa-32617625dbcb
-- title:
--   Universal property of base change for special graded Cartier modules
-- statement:
--   Fix a prime $p$ and commutative rings $S$, $T$, $B'$, each equipped with a ring homomorphism from $\mathbb{W}(\mathbb{F}_{p^2})$ (written `Zp2 p`), namely $jS$, $jT$, $j'$, together with ring homomorphisms $i\colon S\to T$ and $q\colon T\to B'$. Let $DS$, $DT$, $D'$ be graded Cartier module data over $S$, $T$, $B'$ for these structure maps — each consisting of a module $M$ over $\mathbb{W}(\cdot)$ with additive endomorphisms $F$, $V$, a linear $\varpi$ satisfying the usual Cartier relations ($FV=p$, $\varpi^2=p$, $\varpi$ commuting with $F$ and $V$) and a pair of complementary submodules indexed by $\mathrm{Fin}\,2$ shifted by $F$, $V$, $\varpi$ — and assume each is special, i.e. admits a homogeneous $V$-basis $\gamma$ (with $\gamma_i$ in the $i$-th piece, every element written uniquely as $\sum_i [c_i]\gamma_i + V y$) and is $V$-adically complete in the sense that every sequence of digits has a unique $V$-adic sum. Let $g\colon DS.M\to DT.M$ be additive and a base change along $i$: $\mathbb{W}(i)$-semilinear, commuting with $F$, $V$ and $\varpi$, preserving the two pieces, and carrying some homogeneous $V$-basis of $DS$ to a homogeneous $V$-basis of $DT$; let $k\colon DS.M\to D'.M$ be additive and a base change along $q\circ i$ in the same sense. Then there is an additive $h\colon DT.M\to D'.M$ which is a base change along $q$ and satisfies $h(g(x))=k(x)$ for all $x$, and $h$ is the only additive map $h'$ that is $\mathbb{W}(q)$-semilinear, commutes with $V$, and satisfies $h'(g(x))=k(x)$ for all $x$.
--
--   This is the universal property identifying a special graded Cartier module equipped with a base-change map from $DS$ along $i$ with the completed base change $\mathbb{W}(T)\,\widehat{\otimes}_{\mathbb{W}(S)} DS.M$, in the form used in the Čerednik–Drinfeld uniformisation: base changes along $q\circ i$ factor uniquely through base changes along $i$, with uniqueness holding in the larger class of semilinear maps commuting only with $V$. It is invoked in the comparison of canonical $L$-maps with functorial base change maps, in particular over nilpotent and torsion-free bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_baseChange_comp_eq_and_unique
    (p : ℕ) [Fact p.Prime] {S T B' : Type} [CommRing S] [CommRing T] [CommRing B']
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (i : S →+* T) (q : T →+* B')
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (g : DS.M →+ DT.M) (hg : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' i DS DT g)
    (k : DS.M →+ D'.M) (hk : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' (q.comp i) DS D' k) :
    ∃ h : DT.M →+ D'.M,
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DT D' h ∧
      (∀ x : DS.M, h (g x) = k x) ∧
      ∀ h' : DT.M →+ D'.M,
        (∀ (w : WittVector p T) (y : DT.M), h' (w • y) = WittVector.map q w • h' y) →
        (∀ y : DT.M, h' (DT.verschiebung y) = D'.verschiebung (h' y)) →
        (∀ x : DS.M, h' (g x) = k x) → h' = h := by sorry
