-- Prove2me | Theorems.Thm_ConstrNestedLogit_Stitch_equation_2_unique
-- name    : ConstrNestedLogit.Stitch.equation_2_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:36.177978+00:00
-- url     : https://prove2.me/theorems/dabee6b5-c76e-411f-9e7c-cee53401970f
-- title:
--   Equation (2) has a unique root
-- statement:
--   Fix a finite collection of candidate assortments in each nest, with at least one candidate per nest. Let $V_i(S_i)$ be the total preference weight of the products in $S_i$, $R_i(S_i)$ their conditional expected revenue, $\gamma_i\in(0,1]$ the nest dissimilarity, and $v_0>0$ the weight of no purchase. Then there is exactly one real number $z$ satisfying equation (2):
--
--   $$
--   v_0z=\sum_{i\in M}\max_{S_i\in A_i}\left\{V_i(S_i)^{\gamma_i}\bigl(R_i(S_i)-z\bigr)\right\}.
--   $$
--
--   This identifies the scalar value used to combine the candidate assortments. The paper states existence and uniqueness in the paragraph following Lemma 1 without a separate proof.
--
--   **Formalization Note** Nests form a finite type, and each $A_i$ is a nonempty finite set of assortments. Products are indexed from zero. The main model uses $v_{i0}=0$; strictly positive product weights and $v_0>0$ make the probability model well defined. Revenues have no ordering or sign restriction.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 12, paragraph after Lemma 1, equation (2)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Stitch

/-- Section 2, p. 12: equation (2) has a unique solution for nonempty finite candidate
collections. -/
theorem equation_2_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (A : ι → Finset (Finset (Fin n)))
    (hA : ∀ i, (A i).Nonempty)
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1) :
    ∃! z : ℝ, I.v0 * z = ∑ i, (A i).sup' (hA i) (fun S =>
      NestedLogitVariants.LP.nestWeight I i S * (NestedLogitVariants.LP.R I i S - z)) := by sorry

end ConstrNestedLogit.Stitch
