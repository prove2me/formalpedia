-- Prove2me | Theorems.Thm_CandesTao_LowerBound_uniqueness_implies_minimal_sampling_rate
-- name    : CandesTao.LowerBound.uniqueness_implies_minimal_sampling_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:45:39.70093+00:00
-- url     : https://prove2.me/theorems/476d2728-4712-42cd-9aa3-acd4c40be2e0
-- title:
--   Theorem 1.7 — Uniqueness implies a minimal sampling rate
-- statement:
--   Fix integers $1 \le m$ and $1 \le r \le n$, a real $\mu_0 \ge 1$ and $0 < \delta < 1/2$, and assume that $\ell := n/(\mu_0 r)$ is an integer. Observe the entries of $n\times n$ real matrices under the Bernoulli model: the observed set $\Omega \subseteq [n]\times[n]$ contains each entry independently with probability $p = m/n^2$, and $\mathcal{P}_\Omega(X)$ keeps the entries of $X$ in $\Omega$ and sets the others to zero.
--
--   Suppose that at least one of the sampling conditions fails:
--
--   $$m \ge n^2\left(1 - e^{-\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right)}\right) \qquad \text{(I.20)}$$
--
--   $$m \ge (1-\epsilon)\,\mu_0 n r\log\left(\frac{n}{2\delta}\right), \quad \epsilon := \frac12\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right). \qquad \text{(I.21)}$$
--
--   Then, with probability at least $\delta$ over $\Omega$, there are infinitely many pairs $(M, M')$ of $n\times n$ matrices with
--
--   $$M \ne M', \qquad \mathcal{P}_\Omega(M) = \mathcal{P}_\Omega(M'),$$
--
--   both of rank at most $r$ and both obeying the incoherence property (I.18) with parameter $\mu_0$ ($\|P_U e_a\|^2 \le \mu_0 r/n$ and $\|P_V e_b\|^2 \le \mu_0 r/n$ for the column and row spaces).
--
--   Consequently, even knowing the rank bound and the coherence ahead of time, no method that sees only $\mathcal{P}_\Omega(M)$ can recover every such matrix with probability greater than $1-\delta$ unless (I.20) holds; up to the factor $1-\epsilon$, about $\mu_0 n r\log n$ samples are necessary.
--
--   **Formalization Note** The event is "the set of such pairs is infinite", evaluated for each observation set $\Omega$; its probability under the Bernoulli model is the platform's `bernoulliEventProb (m/n²)`. The pairs may depend on $\Omega$, which is the reading the paper proves in Section II and uses in the sentence following the theorem. The integrality of $\ell = n/(\mu_0 r)$ is the paper's own "without loss of generality" of Section II, stated as a hypothesis. The hypothesis "(I.20) fails or (I.21) fails" covers both parts of the theorem. The logarithm is natural. The standing assumptions of Section I-H ($m \ge 2nr$, $n$ larger than an absolute constant) serve the upper bounds and are not imposed; the theorem's own ranges are.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2058, Theorem 1.7 (Uniqueness Implies a Minimal Sampling Rate), Eqs. (I.20), (I.21); incoherence (I.18) on p. 2057; proof in Section II, pp. 2059–2060

import Definitions.Def_CandesTao_LowerBound_Incoherence
import Definitions.Def_CandesTao_LowerBound_SamplingConditions
open MatrixCompletion

namespace CandesTao.LowerBound

theorem uniqueness_implies_minimal_sampling_rate
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (hnot : ¬ SamplingConditionI20 n m r μ₀ δ ∨ ¬ SamplingConditionI21 n m r μ₀ δ) :
    bernoulliEventProb ((m : ℝ) / (n : ℝ) ^ 2)
        (fun Ω : Finset (Fin n × Fin n) =>
          {P : RealMatrix n n × RealMatrix n n |
            P.1 ≠ P.2 ∧ IncoherentRankAtMost r μ₀ P.1 ∧ IncoherentRankAtMost r μ₀ P.2 ∧
              samplingProjection Ω P.1 = samplingProjection Ω P.2}.Infinite) ≥ δ := by sorry

end CandesTao.LowerBound
