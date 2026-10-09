-- Prove2me | Theorems.Thm_CustAssort_AugGreedy_lemma_4_3
-- name    : CustAssort.AugGreedy.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:00.400164+00:00
-- url     : https://prove2.me/theorems/077599ba-dbe3-4e30-84d3-758c0a57df58
-- title:
--   Lemma 4.3 — truncated personalized revenue is submodular
-- statement:
--   Products are ordered by decreasing positive revenue, and MNL preference weights are nonnegative. For any customer type $j$ and product $i$, let $V_i=\{1,\ldots,i\}$ and let $f_j(S)$ be the greatest expected revenue from a subset of $S$. Then
--   $$
--   S\longmapsto\min(f_j(S),r_i)
--   $$
--   is submodular on $V_i$, in the diminishing-marginal sense of the paper's footnote 1.
--
--   This local submodularity property is the reason the objective of each Augmented Greedy iteration has a greedy approximation guarantee.
--
--   **Formalization Note** The statement quantifies over every type $j$, which includes every $j\in C$ in the paper. Lean's index $i$ corresponds to the paper's $i+1$.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), Lemma 4.3, p. 11; proof App. D, pp. 36–38

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

namespace CustAssort.AugGreedy

/-- Lemma 4.3, p. 11: type-j optimal revenue truncated at r_i is submodular on V_i. -/
theorem lemma_4_3 {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hr : ∀ p, 0 < r p) (hv : ∀ p j, 0 ≤ v p j) (hanti : Antitone r)
    (j : Fin m) (i : Fin n) :
    SubmodularOn (fun S => min (fj v r j S) (r i)) (Vset i) := by sorry

end CustAssort.AugGreedy
