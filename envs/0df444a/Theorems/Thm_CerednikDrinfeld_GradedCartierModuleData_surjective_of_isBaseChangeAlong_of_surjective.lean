-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective
-- name    : CerednikDrinfeld.GradedCartierModuleData.surjective_of_isBaseChangeAlong_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/1341ccf0-7983-5e8c-b165-7cd900b93448
-- title:
--   Base change of special Cartier modules along a surjection is onto
-- statement:
--   Let $p$ be a prime, let $B$ and $B'$ be commutative rings, let $j\colon W(\mathbb{F}_{p^2})\to B$ be a ring homomorphism (where `Zp2 p` is $W(\mathbb{F}_{p^2})$ realised as Witt vectors over the field with $p^2$ elements), and let $\varphi\colon B\to B'$ be a surjective ring homomorphism. Let $D$ be graded Cartier module data over $(p,B,j)$ and $D'$ graded Cartier module data over $(p,B',\varphi\circ j)$: each consists of a $W_p(\,\cdot\,)$-module $M$ with additive endomorphisms $F$ (Frobenius-semilinear), $V$ (with $w\cdot Vx=V(F(w)x)$, $V(w\cdot Fx)=V(w)\cdot x$, $FV=p$), a $W_p$-linear $\Pi$ commuting with $F$ and $V$ and satisfying $\Pi^2=p$, and a decomposition of $M$ into two complementary submodules `piece 0`, `piece 1` shifted by each of $F$, $V$, $\Pi$. Assume both are special Cartier modules, i.e. each admits a homogeneous $V$-basis $\gamma\colon \mathrm{Fin}\,2\to M$ (with $\gamma i$ in `piece i`, every element uniquely of the form $\sum_i [c_i]\gamma_i+V y$ with $c_i$ in the base ring and $y\in M$) and is $V$-adically complete (every sequence $(x_m)$ has a unique sum $s$ such that for all $N$, $s-\sum_{m<N}V^m x_m$ lies in the image of $V^N$). Let $f\colon D.M\to D'.M$ be an additive map which is base change along $\varphi$: it is $W_p(\varphi)$-semilinear, commutes with $F$, $V$ and $\Pi$, sends `piece i` into `piece i`, and carries some homogeneous $V$-basis $\gamma$ of $D.M$ to a homogeneous $V$-basis $f\circ\gamma$ of $D'.M$. Then $f$ is surjective.
--
--   This is the surjectivity half of the statement that base change of special graded Cartier modules along a surjection of base rings is onto, as in Boutot–Carayol's $p$-adic uniformisation of Shimura curves (II (3.7)). It is used downstream in the study of the associated $N$-modules and of canonical lifts, in particular in the square-zero and nilpotent-thickening steps for the invariance of $\eta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.surjective_of_isBaseChangeAlong_of_surjective
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f) :
    Function.Surjective f := by sorry
