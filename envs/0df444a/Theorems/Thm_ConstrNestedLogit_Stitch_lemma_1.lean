-- Prove2me | Theorems.Thm_ConstrNestedLogit_Stitch_lemma_1
-- name    : ConstrNestedLogit.Stitch.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:20.054984+00:00
-- url     : https://prove2.me/theorems/dff11061-8947-45a8-9ee0-6004fca493e4
-- title:
--   Lemma 1: the root of equation (2) is the best candidate revenue
-- statement:
--   For each nest $i$, let $A_i$ be a nonempty finite collection of candidate assortments. Suppose $z$ solves equation (2), and select a candidate $\widehat S_i\in A_i$ that maximizes $V_i(S_i)^{\gamma_i}(R_i(S_i)-z)$ in every nest. Then the combined assortment earns exactly $z$, and no combination of candidates earns more:
--
--   $$
--   \Pi(\widehat S_1,\ldots,\widehat S_m)=z,
--   \qquad
--   \Pi(S_1,\ldots,S_m)\le z\quad\text{for every }S_i\in A_i.
--   $$
--
--   This is the finite candidate reduction used to select a global assortment from independent nestwise candidate lists.
--
--   **Formalization Note** The paper's candidates belong to nestwise feasibility sets $C_i$; this statement omits $C_i$ because the conclusion compares only combinations in the stated candidate lists and holds for arbitrary such lists. It assumes $v_0>0$, positive product weights, $v_{i0}=0$, and $\gamma_i\in(0,1]$, with no revenue ordering or sign restriction.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 11–12, Lemma 1, equations (2)–(3)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Stitch

/-- Lemma 1, pp. 11–12: a root of equation (2) is the best revenue among combinations
of candidates, and every combination of local maximizers in (3) attains it. -/
theorem lemma_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (A : ι → Finset (Finset (Fin n)))
    (hA : ∀ i, (A i).Nonempty)
    (z : ℝ) (S_hat : ι → Finset (Fin n))
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (hroot : I.v0 * z = ∑ i, (A i).sup' (hA i) (fun S =>
      NestedLogitVariants.LP.nestWeight I i S * (NestedLogitVariants.LP.R I i S - z)))
    (hmem : ∀ i, S_hat i ∈ A i)
    (hmax : ∀ i S, S ∈ A i →
      NestedLogitVariants.LP.nestWeight I i S * (NestedLogitVariants.LP.R I i S - z) ≤
      NestedLogitVariants.LP.nestWeight I i (S_hat i) *
        (NestedLogitVariants.LP.R I i (S_hat i) - z)) :
    NestedLogitVariants.LP.revenue I S_hat = z ∧
      ∀ S : ι → Finset (Fin n), (∀ i, S i ∈ A i) →
        NestedLogitVariants.LP.revenue I S ≤ z := by sorry

end ConstrNestedLogit.Stitch
