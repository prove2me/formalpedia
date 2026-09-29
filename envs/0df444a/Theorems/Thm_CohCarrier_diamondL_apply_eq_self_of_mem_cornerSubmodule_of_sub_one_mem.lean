-- Prove2me | Theorems.Thm_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem
-- name    : CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/7c5cc9aa-2775-5564-a290-d3f35821a0b0
-- title:
--   Residually trivial diamond operators fix corner submodules
-- statement:
--   Let $\mathcal O$ be a commutative local ring, let $L$ be a positive natural number and let $H \le (\mathbb Z/L)^\times$ be a subgroup whose index $[\,(\mathbb Z/L)^\times : H\,]$, viewed in $\mathcal O$ through the natural map from $\mathbb N$, is a unit. Here $H1\ L\ H\ \mathcal O$ is the group of additive homomorphisms from the additivisation of $\Gamma_H(L) \le \mathrm{SL}_2(\mathbb Z)$ (the image in $\mathrm{SL}_2(\mathbb Z)$ of the preimage of $H$ under the determinant-type character `gamma0Units` on $\Gamma_0(L)$) to $\mathcal O$, and for a unit $d$ the operator `diamondL L H 𝒪 d` is the $\mathcal O$-linear endomorphism given by precomposition with conjugation by a chosen element of $\Gamma_0(L)$ lifting $d$. Let $\mathbb T$ be a commutative $\mathcal O$-algebra, module-finite over $\mathcal O$, acting on $H1\ L\ H\ \mathcal O$ compatibly with the $\mathcal O$-action. Let $Sp$ be an idempotent splitting of $\mathbb T$, that is, data consisting of finitely many complete orthogonal idempotents $e_j$ together with maximal ideals $\mathfrak m_j$ exhausting all maximal ideals of $\mathbb T$ and satisfying $e_j \in \mathfrak m_k \iff j \ne k$, and fix an index $i$. Assume the corner ring `Sp.CornerRing i` acts faithfully on the corner submodule $e_i \cdot H1\ L\ H\ \mathcal O$ (the range of multiplication by $e_i$), in the sense that an element killing every element of that submodule is zero. Let $d \in (\mathbb Z/L)^\times$ and let $t \in \mathbb T$ act on all of $H1\ L\ H\ \mathcal O$ as `diamondL L H 𝒪 d`, with $t - 1 \in \mathfrak m_i$. Then $\langle d\rangle v = v$ for every $v$ in the corner submodule.
--
--   This says that a diamond operator which is residually trivial at the maximal ideal $\mathfrak m_i$ acts trivially on the corresponding corner of $H^1(\Gamma_H(L), \mathcal O)$, so that the corner lies in the invariants of the diamond action of $(\mathbb Z/L)^\times/H$ when the index is prime to the residue characteristic. It is the supply lemma for descending corners from $\Gamma_H(L)$ to $\Gamma_0(L)$ in the auxiliary-prime device, and is used in the construction of the Hecke-local pairing data for cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_CohCarrier_Inst
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier IharaLemma IsLocalRing

theorem CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ)
    (hunit : IsUnit ((H.index : ℕ) : 𝒪))
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L H 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)), x • m = 0) → x = 0)
    (d : (ZMod L)ˣ) (t : 𝕋) (ht : ∀ v : H1 L H 𝒪, t • v = diamondL L H 𝒪 d v) (h1 : t - 1 ∈ Sp.𝔪 i)
    (v : H1 L H 𝒪) (hv : v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)) :
    diamondL L H 𝒪 d v = v := by sorry
