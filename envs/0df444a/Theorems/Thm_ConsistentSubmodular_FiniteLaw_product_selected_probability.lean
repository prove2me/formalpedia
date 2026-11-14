-- Prove2me | Theorems.Thm_ConsistentSubmodular_FiniteLaw_product_selected_probability
-- name    : ConsistentSubmodular.FiniteLaw.product_selected_probability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:25.734594+00:00
-- url     : https://prove2.me/theorems/a3617de4-bc65-4a35-8ee8-c0c919c0c16e
-- title:
--   Selected set under a product law has the Bernoulli product distribution
-- statement:
--   Let $\kappa$ be a finite index type with decidable equality, and for each $i\in\kappa$ let $\mathcal L_i$ be a probability law on a finite set $A_i$, with a selection event $\mathrm{select}_i\subseteq A_i$. Under the product law $\mathcal L=\bigotimes_i\mathcal L_i$, let $\Sigma(\omega)=\{i\in\kappa:\ \omega_i\in\mathrm{select}_i\}$ be the set of selected indices. Put $q_i=\mathcal L_i(\mathrm{select}_i)$. Then for every $S\subseteq\kappa$,
--   $$\mathcal L\bigl(\Sigma=S\bigr)\;=\;\prod_{i\in S}q_i\;\prod_{i\notin S}(1-q_i).$$
--
--   Hence $\Sigma$ is the random set containing each index independently with probability $q_i$. This identifies sampling coordinates independently from a product law with the Bernoulli (independent inclusion) distribution used in the mixtures $H_j(p)$.
--
--   **Formalization Note**: the right-hand side is `bernoulliWeight`, with the product over the complement of $S$ taken in $\kappa$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteProductLaw.lean#L81-L107 (`ConsistentSubmodular.FiniteLaw.product_selected_probability`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : κ → Type*} [∀ i, Fintype (A i)]

theorem ConsistentSubmodular.FiniteLaw.product_selected_probability (laws : ∀ i, FiniteLaw (A i))
    (select : ∀ i, A i → Prop) (S : Finset κ) :
    (product laws).probability (fun ω => selectedSet select ω = S) =
      bernoulliWeight (fun i => (laws i).probability (select i)) S := by sorry
