-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_comp_of_bijective
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.comp_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/dc144e17-3dce-5fd6-b80b-44ee446a338f
-- title:
--   Base change of graded Cartier data composed with an isomorphism
-- statement:
--   Fix a prime $p$ and commutative rings $B$, $B'$, a ring homomorphism $j \colon W(\mathbb{F}_{p^2}) \to B$ (where [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is the Witt vectors of the field with $p^2$ elements) and a ring homomorphism $\varphi \colon B \to B'$. Let $D_1$ be graded Cartier module data over $(p,B,j)$ and let $D_2$, $D_3$ be graded Cartier module data over $(p,B',\varphi \circ j)$; each such datum consists of a module $M$ over $W(p,\cdot)$ with additive operators $F$, $V$, a linear operator $\varpi$ and two complementary submodules $\mathrm{piece}\,0$, $\mathrm{piece}\,1$ satisfying the usual Cartier relations and shifting the grading by $1$. Let $f \colon D_1.M \to D_2.M$ be additive and suppose $f$ is a base change along $\varphi$: it is $\varphi$-semilinear for the induced map $W(p,B) \to W(p,B')$, commutes with $F$, $V$ and $\varpi$, carries $\mathrm{piece}\,i$ into $\mathrm{piece}\,i$, and there is $\gamma \colon \mathrm{Fin}\,2 \to D_1.M$ with $\gamma i \in D_1.\mathrm{piece}\,i$ such that every element of $D_1.M$ is uniquely of the form $\sum_i \tau(c_i)\gamma_i + V y$ with $c \in B^2$, $y \in D_1.M$ ($\tau$ the Teichmüller lift), and such that $f \circ \gamma$ has the same property in $D_2$. Let $g \colon D_2.M \to D_3.M$ be additive, bijective, commuting with the $W(p,B')$-action, with $F$, $V$ and $\varpi$, and carrying $\mathrm{piece}\,i$ into $\mathrm{piece}\,i$. Then $g \circ f$ is a base change of $D_1$ to $D_3$ along $\varphi$.
--
--   The statement records that the property of being a base change of graded Cartier module data along a ring homomorphism is stable under post-composition with an isomorphism of data over the target ring. It is used in the construction of a canonical map from a formal $\mathcal{O}_D$-module to its graded Cartier module data, where the Cartier module of a base-changed formal module is only identified with the expected one up to isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_comp_of_bijective.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.comp_of_bijective
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] (j : CerednikDrinfeld.Zp2 p →+* B)
    (φ : B →+* B')
    (D₁ : CerednikDrinfeld.GradedCartierModuleData p B j)
    (D₂ D₃ : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j))
    (f : D₁.M →+ D₂.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D₁ D₂ f)
    (g : D₂.M →+ D₃.M) (hg : Function.Bijective g)
    (hW : ∀ (w : WittVector p B') (x : D₂.M), g (w • x) = w • g x)
    (hF : ∀ x, g (D₂.frobenius x) = D₃.frobenius (g x))
    (hV : ∀ x, g (D₂.verschiebung x) = D₃.verschiebung (g x))
    (hPi : ∀ x, g (D₂.varpi x) = D₃.varpi (g x))
    (hpc : ∀ (i : Fin 2) (x : D₂.M), x ∈ D₂.piece i → g x ∈ D₃.piece i) :
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D₁ D₃ (g.comp f) := by sorry
