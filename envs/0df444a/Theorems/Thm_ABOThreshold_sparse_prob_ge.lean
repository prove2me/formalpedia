-- Prove2me | Theorems.Thm_ABOThreshold_sparse_prob_ge
-- name    : ABOThreshold.sparse_prob_ge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:41:33.178376+00:00
-- url     : https://prove2.me/theorems/71d07c06-85aa-46f6-bedb-549c70715a4b
-- title:
--   Lemma 10 — doubly exponential decay of the non-sparse probability
-- statement:
--   This is Lemma 10 of the paper. Let $A$ be the maximal number of locations in a rectangle, $k$ the tolerance of a rectangle, and let the error rate satisfy $0<\eta<1$ and $\eta<\eta_c=\binom{A}{k+1}^{-1/k}$.
--
--   Then there exists $\delta>0$ such that for every recursion level $r$ the probability $P(r)$ that the faults in an $r$-rectangle form an $(r,k)$-sparse set obeys
--
--   $$P(r) \;\ge\; 1 - \eta^{(1+\delta)^{r}} .$$
--
--   Because the exponent $(1+\delta)^r$ grows geometrically, the failure probability decays doubly exponentially in the number of levels of concatenation: this is the precise sense in which a constant error rate below the threshold can be driven down to an arbitrarily small effective error rate at polylogarithmic cost.
--
--   **Formalization Note** The paper asserts the strict inequality $P(r)>1-\eta^{(1+\delta)^r}$; at $r=0$ both sides equal $1-\eta$, so the statement is formalized with $\ge$.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, p. 52, Lemma 10

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem sparse_prob_ge (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hlt : η < thresholdProb A k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 - η ^ ((1 + δ) ^ r) ≤ sparseProb A k η r := by sorry

end ABOThreshold
