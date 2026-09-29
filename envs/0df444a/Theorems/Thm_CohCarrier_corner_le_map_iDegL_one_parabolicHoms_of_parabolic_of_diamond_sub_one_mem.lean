-- Prove2me | Theorems.Thm_CohCarrier_corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem
-- name    : CohCarrier.corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/705b75c2-2332-522e-ac50-9db2dcdab8b8
-- title:
--   Corners with residually trivial nebentypus lie in W(M,Hₛ)
-- statement:
--   Fix a commutative ring $\mathcal O$, an integer $M$ (nonzero) and a subgroup $H_s \le (\mathbb Z/M)^\times$, and let $\Gamma_{H_s}(M) =$ `GammaH M Hs` be the preimage in $\Gamma_0(M)$ of $H_s$ under the lower-right-entry character, so that `GammaH M ⊤` $= \Gamma_0(M)$; write $H^1(M,H_s;\mathcal O) =$ `H1 M Hs 𝒪` for the $\mathcal O$-module of additive homomorphisms $\mathrm{Additive}\,\Gamma_{H_s}(M) \to \mathcal O$. Assume given the level datum $h_1 :$ `LevelLE M M ⊤ Hs 1` (that is, $M \mid M$, $1 \mid M/M$, and every unit of $H_s$ reduces into $\top$), and assume the index $[(\mathbb Z/M)^\times : H_s]$ is invertible in $\mathcal O$. Let $\mathbb T$ be a commutative $\mathcal O$-algebra acting on $H^1(M,H_s;\mathcal O)$ compatibly with the $\mathcal O$-action, let `Sp` be an idempotent splitting of $\mathbb T$ — a finite family of complete orthogonal idempotents $e_j$ together with maximal ideals $\mathfrak m_j$ exhausting all maximal ideals and satisfying $e_j \in \mathfrak m_k \iff j \neq k$ — and fix an index $i$. Suppose (i) every $v$ in the corner $e_i \cdot H^1(M,H_s;\mathcal O)$, i.e. in the range of multiplication by $e_i$, is parabolic, meaning $v(\gamma) = 0$ for all $\gamma \in \Gamma_{H_s}(M)$ with $\mathrm{tr}(\gamma)^2 = 4$; and (ii) for every $d \in (\mathbb Z/M)^\times$ there is $g \in \mathbb T$ acting on $H^1(M,H_s;\mathcal O)$ exactly as the diamond operator `diamondL M Hs 𝒪 d` and with $g - 1 \in \mathfrak m_i$. Then every $v$ in that corner lies in the image of the submodule of parabolic homomorphisms on $\Gamma_0(M)$ under the degeneracy pullback `iDegL M M ⊤ Hs 1 𝒪 𝒪 h₁`.
--
--   This identifies the local component of $H^1(\Gamma_{H_s}(M),\mathcal O)$ cut out by an idempotent with residually trivial nebentypus as a submodule of $W(M,H_s)$, the image of the parabolic cohomology of $\Gamma_0(M)$ under the degeneracy map; the criterion used is that membership in this image is equivalent to being parabolic and invariant under all diamond operators. It serves the Taylor–Wiles style passage to auxiliary levels, and is invoked in the constructions of Hecke-local corner data and their refinements at levels divisible by the auxiliary primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier
open IharaLemma

theorem CohCarrier.corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem
    {𝒪 : Type} [CommRing 𝒪] (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ Hs 1)
    (hunit : IsUnit ((Hs.index : ℕ) : 𝒪))
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M Hs 𝒪)]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    (hpar : ∀ v : H1 M Hs 𝒪, v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i) →
      v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪)
    (hneb : ∀ d : (ZMod M)ˣ, ∃ g : 𝕋, (∀ v : H1 M Hs 𝒪, g • v = diamondL M Hs 𝒪 d v) ∧ g - 1 ∈ Sp.𝔪 i) :
    ∀ v : H1 M Hs 𝒪, v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ Hs 1 𝒪 𝒪 h₁) := by sorry
