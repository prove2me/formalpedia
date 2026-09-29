-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange
-- name    : CerednikDrinfeld.GradedCartierModuleData.isHomogeneousVBasis_map_of_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/c8a4f819-b9fd-5b63-b22a-42072c9330ec
-- title:
--   Base change carries homogeneous V-bases to homogeneous V-bases
-- statement:
--   Fix a prime $p$ and commutative rings $S$ and $B$, each equipped with a ring homomorphism from $\mathrm{Zp2}\,p = W(\mathbb{F}_{p^2})$, say $j_S$ and $j$, and let $\varphi : S \to B$ be a ring homomorphism. Let $DS$ be graded Cartier module data over $S$ (a $W(p,S)$-module $DS.M$ with additive operators $F$, $V$, a $W(p,S)$-linear $\varpi$ satisfying the Cartier relations $F(w\cdot x)=\sigma(w)F(x)$, $w\,V(x)=V(\sigma(w)x)$, $V(w\,F(x))=V(w)\,x$, $F V=p$, $\varpi V=V\varpi$, $\varpi F=F\varpi$, $\varpi^2=p$, together with complementary submodules $DS.\mathrm{piece}\,0$, $DS.\mathrm{piece}\,1$ shifted by each of $F$, $V$, $\varpi$), and similarly let $D$ be such data over $B$; both are assumed to be special, i.e. to admit a homogeneous $V$-basis and to be $V$-adically complete in the sense of the project's predicates. Let $f : DS.M \to D.M$ be an additive map which is base change along $\varphi$: it is $W(\varphi)$-semilinear, commutes with $F$, $V$ and $\varpi$, preserves the grading pieces, and carries some homogeneous $V$-basis of $DS$ to a homogeneous $V$-basis of $D$. Then for every homogeneous $V$-basis $\gamma = (\gamma_0,\gamma_1)$ of $DS$ (so $\gamma_i \in DS.\mathrm{piece}\,i$ and every $x \in DS.M$ is uniquely $\sum_i [c_i]\gamma_i + V y$ with $c_i \in S$, $y \in DS.M$), the pair $(f(\gamma_0), f(\gamma_1))$ is a homogeneous $V$-basis of $D$: $f(\gamma_i) \in D.\mathrm{piece}\,i$, and every $x \in D.M$ has a unique expression $x = \sum_{i} [c_i]\,f(\gamma_i) + V y$ with $c_i \in B$ and $y \in D.M$, where $[\,\cdot\,]$ denotes the Teichmüller lift.
--
--   This upgrades the base-change predicate, whose basis clause asserts the conclusion for one homogeneous $V$-basis only, to all homogeneous $V$-bases, so that base-change maps can be composed and transported. It is used in the construction and naturality of the canonical maps attached to special formal modules in the Čerednik–Drinfeld uniformisation, in particular when pushing a lift of a special module along a further ring homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.isHomogeneousVBasis_map_of_baseChange
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B} (φ : S →+* B)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : DS.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ DS D f)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ) :
    D.IsHomogeneousVBasis (fun i => f (γ i)) := by sorry
