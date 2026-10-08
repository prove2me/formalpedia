-- Prove2me | Theorems.Thm_ChoiceRM_Policy_lemma_2
-- name    : ChoiceRM.Policy.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:42.119533+00:00
-- url     : https://prove2.me/theorems/6bd1e552-d273-4748-8146-c23d1f0529ab
-- title:
--   Lemma 2, p. 12 — largest optimal index decreases with marginal value
-- statement:
--   For an ordered family of nondominated sets, let $k^*(v)$ be the greatest index maximizing $R_k-Q_kv$. If $0\le v\le v'$, then
--
--   $$k^*(v')\le k^*(v).$$
--
--   The greatest-index convention resolves ties and is the one used by Theorem 1. In the dynamic program, $v$ is the marginal capacity value $\Delta V_{t-1}(x)$.
--
--   **Formalization Note** The statement uses the real parameter $v$ introduced in the paper's proof of Lemma 2. Its two maximizers are required to be the greatest among ties.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), pp. 12–13, Lemma 2 and proof

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
import Definitions.Def_ChoiceRM_Policy_Value

namespace ChoiceRM.Policy

open RevenueManagement

/-- Lemma 2 (p. 12): the greatest optimal index decreases with the marginal value. -/
theorem lemma_2 {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (Sq : Fin m → Finset (Fin n)) (hnd : ∀ k, IsNondominated P r (Sq k))
    (hmono : Monotone (fun k => purchaseProb P (Sq k)))
    (v v' : ℝ) (hv : 0 ≤ v) (hvv' : v ≤ v') (k k' : Fin m)
    (hk : IsLargestMaximizer P r Sq v k)
    (hk' : IsLargestMaximizer P r Sq v' k') :
    k' ≤ k := by sorry

end ChoiceRM.Policy
