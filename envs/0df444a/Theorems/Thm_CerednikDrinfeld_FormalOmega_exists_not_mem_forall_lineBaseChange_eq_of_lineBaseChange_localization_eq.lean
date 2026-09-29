-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
-- name    : CerednikDrinfeld.FormalOmega.exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/b632617e-7509-52b6-b2c3-213084b3483a
-- title:
--   Equality of base-changed lines spreads to a basic open
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K_0$ a field which is an $\mathcal O$-algebra, and $B$ a commutative $\mathcal O$-algebra. Let $M$ be a full lattice over $\mathcal O$ in $K_0^2$, that is, a finitely generated $\mathcal O$-submodule $M$ of $\mathrm{Fin}\,2 \to K_0$ whose $K_0$-span is everything. Write $B \otimes_{\mathcal O} M$ for the base change `latticeBaseChange`, and let $N_1, N_2$ be $B$-submodules of $B \otimes_{\mathcal O} M$ such that each quotient $(B \otimes_{\mathcal O} M)/N_i$ is an invertible $B$-module. For an $\mathcal O$-algebra map $\varphi : B \to B'$, `lineBaseChange` sends a submodule $N$ to the $B'$-span of the image of $N$ under $\varphi \otimes \mathrm{id}_M$ inside $B' \otimes_{\mathcal O} M$. Let $\mathfrak p$ be a prime ideal of $B$ and assume that the base changes of $N_1$ and $N_2$ along the localisation map $B \to B_{\mathfrak p}$ coincide as submodules of $B_{\mathfrak p} \otimes_{\mathcal O} M$. The conclusion is that there exists $f \in B$ with $f \notin \mathfrak p$ such that for every commutative ring $C$ which is an $\mathcal O$-algebra and a $B$-algebra with compatible structures, and which is a localisation of $B$ away from $f$, the base changes of $N_1$ and $N_2$ along $B \to C$ coincide in $C \otimes_{\mathcal O} M$.
--
--   This is the standard spreading-out principle for localisations: an equality of finitely generated submodules valid after localising at a prime already holds over a basic open neighbourhood of that prime. It is used in the Čerednik–Drinfeld gluing construction, where it supplies the finite open covers over which two prescribed kernel lines on a base-changed lattice agree, and it is cited by [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_finite_cover_isPullback_of_zeta_comp_eq`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_finite_cover_isPullback_of_zeta_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K₀)
    (N₁ N₂ : Submodule B (latticeBaseChange 𝒪 K₀ B M))
    (h₁ : Module.Invertible B (latticeBaseChange 𝒪 K₀ B M ⧸ N₁))
    (h₂ : Module.Invertible B (latticeBaseChange 𝒪 K₀ B M ⧸ N₂))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime 𝔭)) M N₁ =
      lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime 𝔭)) M N₂) :
    ∃ f : B, f ∉ 𝔭 ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away f C],
        lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₁ = lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₂ := by sorry
