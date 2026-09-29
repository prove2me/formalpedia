-- Prove2me | Theorems.Thm_ABOThreshold_threshold_recursion_depth
-- name    : ABOThreshold.threshold_recursion_depth
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:42:47.923442+00:00
-- url     : https://prove2.me/theorems/2636c6da-9e5a-4f44-91aa-ea9b09757e19
-- title:
--   Threshold theorem (probabilistic noise): polylogarithmic recursion depth suffices
-- statement:
--   This is the quantitative core of Theorem 10, the threshold theorem for probabilistic noise.
--
--   Fix a rectangle size $A$ and a tolerance $k\ge1$ with $k+1\le A$, and an error rate $\eta$ below the threshold $\eta_c=\binom{A}{k+1}^{-1/k}$. Then there are constants $C,c>0$, depending only on $A$, $k$ and $\eta$, such that for every circuit with $v\ge1$ locations and every target accuracy $0<\varepsilon<1$ there is a number of concatenation levels $r$ with
--
--   $$v\cdot\bigl(1-P(r)\bigr) \;<\; \varepsilon \qquad\text{and}\qquad A^{r} \;\le\; C\Bigl(1+\log\frac{v}{\varepsilon}\Bigr)^{c} .$$
--
--   The first inequality is the statement that, after $r$ levels of recursive simulation, the probability that any of the $v$ rectangles of the computation carries a non-sparse fault path — the event that the proof of Theorem 10 must exclude — is smaller than $\varepsilon$. The second inequality is the cost: the number of physical locations simulating one original location, $A^{r}$, is polylogarithmic in $v/\varepsilon$, which is exactly the $\log^{c}(v/\varepsilon)$ overhead in space, time and gate count claimed by Theorem 10.
--
--   Together they express the content of the theorem at the level of the noise analysis: below a constant threshold, an arbitrarily reliable simulation is bought with polylogarithmic overhead. The circuit-level formulation of Theorem 10 — the existence of a simulating circuit $Q'$ computing a function $\varepsilon$-close to that of $Q$ — additionally requires a formal model of quantum circuits with mixed states, fault-tolerant procedures and quantum codes, which is outside the scope of this mission.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, p. 52, Theorem 10 and Lemma 10 (quantitative core of the proof)

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem threshold_recursion_depth (A k : ℕ) (hk : 1 ≤ k) (hA : k + 1 ≤ A) (η : ℝ) (hη : 0 < η)
    (hlt : η < thresholdProb A k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (v : ℕ) (ε : ℝ), 1 ≤ v → 0 < ε → ε < 1 →
      ∃ r : ℕ, (v : ℝ) * badProb A k η r < ε ∧
        (A : ℝ) ^ r ≤ C * (1 + Real.log ((v : ℝ) / ε)) ^ c := by sorry

end ABOThreshold
