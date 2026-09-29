-- Prove2me | Theorems.Thm_AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq
-- name    : AdicCompletion.ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/7c3f07d7-5807-5d82-b9e3-5592fd1b4bb5
-- title:
--   Local homomorphisms out of an adic completion agree on R
-- statement:
--   Let $R$ be a commutative Noetherian local ring with maximal ideal $\mathfrak m =$ `maximalIdeal R`, and let $\hat R =$ `AdicCompletion (maximalIdeal R) R` denote its $\mathfrak m$-adic completion, an $R$-algebra via `algebraMap`. Let $T$ be a commutative local ring with maximal ideal $\mathfrak m_T$, assumed Hausdorff for the $\mathfrak m_T$-adic filtration, i.e. `IsHausdorff (maximalIdeal T) T`, so that an element congruent to $0$ modulo $\mathfrak m_T^n$ for every $n$ is $0$. Let $g_1, g_2 : \hat R \to T$ be ring homomorphisms, each local in the sense that every element of the maximal ideal of $\hat R$ is carried into $\mathfrak m_T$, and suppose that $g_1$ and $g_2$ agree on the image of $R$, i.e. $g_1(\iota(r)) = g_2(\iota(r))$ for all $r \in R$, where $\iota$ is the structure map $R \to \hat R$. The conclusion is the equality $g_1 = g_2$ of ring homomorphisms. No completeness assumption on $T$, and no Noetherian assumption on $T$, is imposed.
--
--   This is the uniqueness half of the statement that a local homomorphism from the adic completion of a Noetherian local ring is determined by its restriction along $R \to \hat R$; the separatedness of $T$ replaces the Krull intersection theorem that would supply it when $T$ is Noetherian local. It is used in the construction of Drinfeld charts on modular curves at full level, where two homomorphisms out of a completed local ring arising from inertia at a cyclotomic place must be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq.lean

import Mathlib
import Definitions.Def_AdicCompletionLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type*} [CommRing T] [IsLocalRing T] [IsHausdorff (maximalIdeal T) T]
    (g₁ g₂ : AdicCompletion (maximalIdeal R) R →+* T)
    (hg₁ : ∀ x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g₁ x ∈ maximalIdeal T)
    (hg₂ : ∀ x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g₂ x ∈ maximalIdeal T)
    (h : ∀ r : R, g₁ (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      g₂ (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) :
    g₁ = g₂ := by sorry
