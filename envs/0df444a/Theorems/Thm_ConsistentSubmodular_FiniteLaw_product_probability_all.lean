-- Prove2me | Theorems.Thm_ConsistentSubmodular_FiniteLaw_product_probability_all
-- name    : ConsistentSubmodular.FiniteLaw.product_probability_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:28.216449+00:00
-- url     : https://prove2.me/theorems/1a5943ec-fc31-4bab-9e93-f767d40e0ae2
-- title:
--   Probability of a product event under a product law
-- statement:
--   Let $\kappa$ be a finite index type and, for each $i\in\kappa$, let $\mathcal L_i$ be a probability law on a finite set $A_i$. Let $\mathcal L=\bigotimes_i\mathcal L_i$ be the product law on $\prod_i A_i$, with weight $\prod_i\mathcal L_i(\omega_i)$ at $\omega=(\omega_i)_i$. For each $i$ let $E_i\subseteq A_i$ be an event. Then
--   $$\mathcal L\bigl(\forall i:\ \omega_i\in E_i\bigr)\;=\;\prod_{i\in\kappa}\mathcal L_i(E_i).$$
--
--   This is the independence property of the product law for a conjunction of coordinate events, and is a basic tool when sampling coordinates independently.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteProductLaw.lean#L60-L75 (`ConsistentSubmodular.FiniteLaw.product_probability_all`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : κ → Type*} [∀ i, Fintype (A i)]

theorem ConsistentSubmodular.FiniteLaw.product_probability_all (laws : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (product laws).probability (fun ω => ∀ i, E i (ω i)) = ∏ i, (laws i).probability (E i) := by sorry
