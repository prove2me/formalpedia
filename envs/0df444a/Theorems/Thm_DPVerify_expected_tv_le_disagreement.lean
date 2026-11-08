-- Prove2me | Theorems.Thm_DPVerify_expected_tv_le_disagreement
-- name    : DPVerify.expected_tv_le_disagreement
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:15.860175+00:00
-- url     : https://prove2.me/theorems/1670657e-f736-4f68-ac70-127dcf3cc813
-- title:
--   Proof of Theorem 4.1, p.12 — $\mathbb E_Sd_{TV}(p_S,\mu)\le\Pr[\mathcal A(S,r)\ne\mathcal A(S',r)]\le\rho$
-- statement:
--   Let $\mathcal A$ be a randomized algorithm with internal randomness $r$ and a finite output space $\mathcal M$, and let $D$ be a distribution on $\mathcal X$. For a sample $S$ let $p_S(m)=\Pr_r[\mathcal A(S,r)=m]$, and let $\mu(m)=\mathbb E_{S\sim D^s}p_S(m)$. Then
--
--   1. $$\mathbb E_{S\sim D^s}\,d_{TV}(p_S,\mu)\;\le\;\Pr_{S,S'\sim D^s,\,r}\bigl[\mathcal A(S,r)\ne\mathcal A(S',r)\bigr],$$
--   2. and if $\mathcal A$ is $\rho$-replicable at $D$, then $\mathbb E_{S\sim D^s}\,d_{TV}(p_S,\mu)\le\rho$.
--
--   Here $d_{TV}(p,q)=\tfrac12\sum_m|p(m)-q(m)|$. In Theorem 4.1 this bounds the cost of letting the prover pick the message from the average law $\mu$ instead of the sample's own law $p_S$, in both the completeness and the soundness analysis.
--
--   Differences from the source:
--   - generalization: $\mathcal A(S,r)$ the verifier's message algorithm → any randomized algorithm with a finite output space; reason: the message algorithm is an instance
--   - encoding: $d_{TV}(p_S,\mu)$ → $\tfrac12\sum_m|p_S(m)-\mu(m)|$ with real probabilities; reason: the definition of total variation on a finite set
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- §4, proof of Theorem 4.1, the replicability display (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.12 = PDF p.15):
`E_S d_TV(p_S, μ) ≤ Pr_{S,S′∼D^s, r}[A(S, r) ≠ A(S′, r)] ≤ ρ`, where `p_S` is the law of `A(S, r)`
over the coins and `μ(m) = E_{S∼D^s} p_S(m)`.

For a randomized algorithm `A` with finite output space `M` and a distribution `D`:
1. `E_S d_TV(p_S, μ)` is at most the probability that two runs on independent samples with shared
   coins disagree;
2. if `A` is `ρ`-replicable at `D`, then `E_S d_TV(p_S, μ) ≤ ρ`.

**Formalization Note** `d_TV(p, q) = (1/2) ∑_m |p(m) − q(m)|` on the finite space `M`; the
probabilities `p_S(m)` are real numbers. -/
theorem expected_tv_le_disagreement (X M : Type) [MeasurableSpace X] [Fintype M]
    [MeasurableSpace M] [DiscreteMeasurableSpace M] (s : ℕ) (A : RandAlg X M s)
    (D : ProbabilityMeasure X) :
    (∫ S, (1 / 2 : ℝ) * ∑ m, |(A.law S {m}).toReal -
        ∫ S', (A.law S' {m}).toReal ∂(Measure.pi fun _ : Fin s => (D : Measure X))|
        ∂(Measure.pi fun _ : Fin s => (D : Measure X))) ≤
      (((Measure.pi fun _ : Fin s => (D : Measure X)).prod
          ((Measure.pi fun _ : Fin s => (D : Measure X)).prod A.P))
        {q | A.run q.1 q.2.2 ≠ A.run q.2.1 q.2.2}).toReal ∧
    ∀ ρ : ℝ, IsReplicableAt A D ρ →
      (∫ S, (1 / 2 : ℝ) * ∑ m, |(A.law S {m}).toReal -
          ∫ S', (A.law S' {m}).toReal ∂(Measure.pi fun _ : Fin s => (D : Measure X))|
          ∂(Measure.pi fun _ : Fin s => (D : Measure X))) ≤ ρ := by sorry

end DPVerify
