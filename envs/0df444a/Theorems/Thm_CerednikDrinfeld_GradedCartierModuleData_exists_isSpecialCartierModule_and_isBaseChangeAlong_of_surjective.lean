-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/64c10999-d5d1-5a3f-a45f-53962c00b1ea
-- title:
--   Base change of special graded Cartier modules along surjections
-- statement:
--   Let $p$ be a prime, let $B$ and $C$ be commutative rings, let $j \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B$ be a ring homomorphism, and let $\psi \colon B \to C$ be a surjective ring homomorphism. Let $D$ be a `GradedCartierModuleData` for $(p, B, j)$: a $W(B)$-module $M$ with additive endomorphisms $F$ and $V$, a $W(B)$-linear endomorphism $\varpi$, and submodules $M_0, M_1$, subject to $F(w \cdot x) = F(w) \cdot F(x)$, $w \cdot V(x) = V(F(w) \cdot x)$, $V(w \cdot F(x)) = V(w) \cdot x$, $F(V(x)) = p\,x$, commutation of $\varpi$ with $F$ and $V$, $\varpi^2 = p$, complementarity of $M_0$ and $M_1$, and the condition that $F$, $V$ and $\varpi$ carry $M_i$ into $M_{i+1}$. Assume $D$ is special: it admits a homogeneous $V$-basis, i.e. a $\gamma$ with $\gamma_i \in M_i$ such that every $x \in M$ is uniquely of the form $\sum_i \tau(c_i)\gamma_i + V(y)$ with $c \in B^2$, $y \in M$ ($\tau$ the Teichmüller lift), and it is $V$-adically complete in the sense that every sequence $(x_m)_{m \in \mathbb{N}}$ in $M$ has a unique sum $s$ with $s \in \sum_{m < N} V^m(x_m) + V^N(M)$ for all $N$. Then there exist such data $D_1$ for $(p, C, \psi \circ j)$ and an additive map $g \colon M \to D_1.M$ such that $D_1$ is again special, $g$ is a base change along $\psi$ — it is semilinear for $W(\psi)$, commutes with $F$, $V$ and $\varpi$, maps each $M_i$ into the $i$-th piece of $D_1$, and carries some homogeneous $V$-basis of $D$ to a homogeneous $V$-basis of $D_1$ — and moreover $g$ carries every homogeneous $V$-basis $\gamma$ of $D$ to a homogeneous $V$-basis $(g(\gamma_i))_i$ of $D_1$.
--
--   This is the surjective case of the base change $M \,\widehat\otimes_{E(B)} E(C)$ of special graded Cartier modules used in the Čerednik–Drinfeld uniformisation, following Boutot–Carayol; the final clause, that every homogeneous $V$-basis and not merely one is carried to a homogeneous $V$-basis, is stronger than the base-change property itself. It is used in the proof that the comparison map from formal $\mathcal{O}_D$-modules to graded Cartier modules is bijective over surjections with nilpotent kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
    (p : ℕ) [Fact p.Prime] {B C : Type} [CommRing B] [CommRing C]
    (j : CerednikDrinfeld.Zp2 p →+* B) (ψ : B →+* C) (hψ : Function.Surjective ψ)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃ (D₁ : CerednikDrinfeld.GradedCartierModuleData p C (ψ.comp j)) (g : D.M →+ D₁.M),
      D₁.IsSpecialCartierModule ∧
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong ψ D D₁ g ∧
      ∀ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ → D₁.IsHomogeneousVBasis (fun i => g (γ i)) := by sorry
