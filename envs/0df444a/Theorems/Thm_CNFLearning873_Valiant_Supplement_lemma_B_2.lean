-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_lemma_B_2
-- name    : CNFLearning873.Valiant.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:40:30.335266+00:00
-- url     : https://prove2.me/theorems/59ee2002-f69a-476d-af83-d2eec5b92af8
-- title:
--   Lemma B.2 (used in the proof of Theorem 6.2) — both gadget count bounds
-- statement:
--   For integers $k\ge3$ and $\ell>0$, let $N_\ell$ count the satisfying assignments of the unrestricted gadget of Definition B.1, and let $\lambda_k=2^{k-1}-1+\sqrt{2^{k-1}(2^{k-1}-k)}$. Then both bounds hold:
--
--   $$\lambda_k^\ell\le N_\ell\le2\lambda_k^\ell.$$
--
--   The count refers to the actual layered CNF, including all unrestricted first-layer assignments. The estimate supports the information-theoretic lower bound of Theorem 6.2.
--
--   Differences from the source:
--   - encoding: k variables in each of ell named layers → flattened variables Fin (k*ell), with printed layer i+1 encoded as i; reason: a bijective relabeling preserves the actual CNF and both exact count bounds
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Lemma B.2, printed p.36 = 1-based PDF p.36; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_GadgetB

namespace CNFLearning873.Valiant.Supplement

/-- Lemma B.2, p.36 = PDF p.36, for the actual unrestricted gadget of Definition B.1. -/
theorem lemma_B_2 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 0 < ℓ) :
    eigenvalue k ^ ℓ ≤ (gadgetCount k ℓ : ℝ) ∧
    (gadgetCount k ℓ : ℝ) ≤ 2 * eigenvalue k ^ ℓ := by sorry

end CNFLearning873.Valiant.Supplement
