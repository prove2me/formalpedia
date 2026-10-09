-- Prove2me | Theorems.Thm_CustAssort_AugGreedy_lemma_E_1
-- name    : CustAssort.AugGreedy.lemma_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:05.321982+00:00
-- url     : https://prove2.me/theorems/a13e0e80-3338-4267-8f63-0fd0c471bad2
-- title:
--   Lemma E.1 — the MNL revenue-threshold assortment is optimal
-- statement:
--   Let $U$ be a finite product universe, with nonnegative MNL preference weights $w_i$ and revenues $r_i$. The no-purchase weight is one. Write $R(S)$ for the expected revenue of an offered assortment $S\subseteq U$, and set $z^*=\max_{S\subseteq U}R(S)$. Then the full revenue-threshold assortment attains the optimum:
--   $$
--   R(\{i\in U:r_i\ge z^*\})=z^*.
--   $$
--   This identifies a concrete optimal assortment used in the submodularity lemma and in the definition of complete customer types.
--
--   **Formalization Note** The finite universe $U$ generalizes the paper's $N$, allowing application to any available assortment. Positivity of revenues is unnecessary for this characterization; nonnegative preference weights are required by the MNL model.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), App. E, problem (E.1), pp. 38–39, Lemma E.1, p. 39

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

namespace CustAssort.AugGreedy

/-- Lemma E.1, p. 39, on a finite universe U: the full revenue-threshold set is optimal. -/
theorem lemma_E_1 {ι : Type*} [DecidableEq ι] (U : Finset ι) (w r : ι → ℝ)
    (hw : ∀ i ∈ U, 0 ≤ w i) :
    let zstar := U.powerset.sup' (Finset.powerset_nonempty U)
      (ChoiceCDLP.MNL.mnlObjective w r 1)
    ChoiceCDLP.MNL.mnlObjective w r 1 (U.filter (fun i => zstar ≤ r i)) = zstar := by sorry

end CustAssort.AugGreedy
