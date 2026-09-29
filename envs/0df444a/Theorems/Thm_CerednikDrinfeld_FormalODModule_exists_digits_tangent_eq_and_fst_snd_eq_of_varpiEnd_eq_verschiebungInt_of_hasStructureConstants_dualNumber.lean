-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
-- name    : CerednikDrinfeld.FormalODModule.exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/fb142cb1-9f6e-5b66-aac8-35a7bf58e994
-- title:
--   Digit relations for a Pi=V invariant over dual numbers
-- statement:
--   Let $p$ be a prime, $\kappa$ a field of characteristic $p$, and $j \colon W(\mathbb{F}_{p^2}) \to \kappa[\varepsilon]$ a ring homomorphism into the dual numbers. Let $X$ be a formal $\mathcal{O}_D$-module over $\kappa[\varepsilon]$, i.e. a commutative two-dimensional formal group law $X.F$ together with an action of $W(\mathbb{F}_{p^2})$ and a uniformiser series $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Let $\gamma = (\gamma_0,\gamma_1)$ be elements of the Cartier module of $X.F$ forming a homogeneous $V$-basis relative to $j$: each $\gamma_i$ lies in the $i$-th graded piece (for every $c \in \mathbb{F}_{p^2}$, the endomorphism induced by the Teichmüller lift of $c$ acts on $\gamma_i$ as the homothety by $j(\tau c)^{p^i}$), and the matrix of tangent coordinates of the $\gamma_i$ has unit determinant. Let $a, \nu \colon \mathbb{N} \to \mathrm{Fin}\,2 \to \kappa$ be such that $\gamma$ has structure constants $A_{m,i} = a_{m,i} + \nu_{m,i}\varepsilon$, meaning that for each $i$ and each $N$ there is $h$ in the Cartier module with $\Pi \gamma_i = \sum_{m<N} V^m\bigl([A_{m,i}]\gamma_{\pi(m,i)}\bigr) + V^N h$, where $\Pi$ denotes the action of $\varpi$ on the Cartier module, $V$ the Verschiebung, $[\,\cdot\,]$ the homothety, and $\pi(m,i) = (m+i+1) \bmod 2$. Assume $\nu_{0,i} = 0$ for both $i$, fix an index $i_0$ with $a_{0,i_0} = 0$, and let $m$ lie in the $i_0$-th graded piece and satisfy $\Pi m = V m$. Then there exist $\delta_0, \delta_1 \in \kappa[\varepsilon]$ and $t$ in the Cartier module such that, writing $i_1 = \pi(0,i_0)$ for the other index: $m = [\delta_0]\gamma_{i_0} + V([\delta_1]\gamma_{i_1} + V t)$; the tangent vector of $m$ is $\delta_0$ times that of $\gamma_{i_0}$ coordinatewise; $\delta_0^{p} A_{1,i_0} + \delta_1 A_{0,i_1} = \delta_0$ and $\delta_0^{p^2} A_{2,i_0} + \delta_1^{p} A_{1,i_1} = \delta_1$; and, with $y$ the first and $y'$ the second component of $\delta_0$, the two relations in $\kappa$
--   $$a_{0,i_1}^{p} y = (a_{0,i_1}^{p}a_{1,i_0} + a_{0,i_1}a_{1,i_1})y^{p} + (a_{0,i_1}^{p+1}a_{2,i_0} - a_{0,i_1}a_{1,i_0}^{p}a_{1,i_1})y^{p^2},$$
--   $$a_{0,i_1}^{p} y' = (a_{0,i_1}^{p+1}\nu_{2,i_0} - a_{0,i_1}a_{1,i_0}^{p}\nu_{1,i_1})y^{p^2} + (a_{0,i_1}^{p}\nu_{1,i_0} + a_{0,i_1}\nu_{1,i_1})y^{p}$$
--   hold.
--
--   This is the first-order (dual number) period relation at a critical index in the Čerednik–Drinfeld theory of special formal $\mathcal{O}_D$-modules: the $V$-adic digit expansion of an element fixed by $\Pi = V$ is cut off after two digits, and the resulting equations split into their $\varepsilon^0$- and $\varepsilon^1$-parts. It feeds the analysis of the $\varepsilon$-variation of tangent coordinates on the $\Pi = V$ locus, being used in [`CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber`](thm.html#CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber); the proof passes through the graded Cartier module data attached to $X$, using that the two graded pieces are complementary over a ring in which $p$ is nilpotent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber.lean

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

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (a ν : ℕ → Fin 2 → κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + ν m i • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i₀ : ℕ))
    (hinv : endAct X.varpiEnd m = verschiebungInt m) :
    ∃ (δ₀ δ₁ : DualNumber κ) (t : CartierModule p X.F),
      m = homothety δ₀ (γ i₀) + verschiebungInt (homothety δ₁ (γ (FormalODModule.piIndex 0 i₀)) + verschiebungInt t) ∧
      (tangent m = fun k => δ₀ * tangent (γ i₀) k) ∧
      δ₀ ^ p * (algebraMap κ (DualNumber κ) (a 1 i₀) + ν 1 i₀ • DualNumber.eps) +
        δ₁ * (algebraMap κ (DualNumber κ) (a 0 (FormalODModule.piIndex 0 i₀)) + ν 0 (FormalODModule.piIndex 0 i₀) • DualNumber.eps) = δ₀ ∧
      δ₀ ^ (p ^ 2) * (algebraMap κ (DualNumber κ) (a 2 i₀) + ν 2 i₀ • DualNumber.eps) +
        δ₁ ^ p * (algebraMap κ (DualNumber κ) (a 1 (FormalODModule.piIndex 0 i₀)) + ν 1 (FormalODModule.piIndex 0 i₀) • DualNumber.eps) = δ₁ ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.fst δ₀ =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * a 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ p +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * a 2 i₀ - a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.snd δ₀ =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * ν 2 i₀ - a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * ν 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ p := by sorry
