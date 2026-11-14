-- Prove2me | Theorems.Thm_BilateralProfitLB_claim_3_6
-- name    : BilateralProfitLB.claim_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:26.514258+00:00
-- url     : https://prove2.me/theorems/7e96b9be-dbd2-4caf-9b02-03bc12d3ce75
-- title:
--   Claim 3.6 — $\mathbb E^j[N_j]-\mathbb E^0[N_j]\le\frac{T}{22K^2}\sqrt{\mathbb E^0[N_j]}$ for deterministic two-bit algorithms
-- statement:
--   Let $K\ge1$, $j\in\{1,\dots,K\}$ and $T\ge0$. Let $\mathcal A$ be a deterministic posted-price algorithm with two-bit feedback: in each round it posts $(p_t,q_t)\in[0,1]^2$ as a function of the past feedback pairs $\big(\mathbb 1\{s_\tau\le p_\tau\},\mathbb 1\{q_\tau\le b_\tau\}\big)$, $\tau<t$. Let $N_j$ be the number of rounds $t\in\{1,\dots,T\}$ in which $q_t\in I_j$, and write $\mathbb E^j$ ($\mathbb E^0$) for the expectation when the valuations are i.i.d. with law $\mathcal D_j$ ($\mathcal D_0$). Then
--   $$\mathbb E^j[N_j]-\mathbb E^0[N_j]\le\frac{T}{22K^2}\sqrt{\mathbb E^0[N_j]}.$$
--
--   An algorithm can tell $\mathcal D_j$ from $\mathcal D_0$ only by posting buyer prices in $I_j$, and each such query carries little information; this is the information-theoretic core of the lower bound.
--
--   **Formalization Note** A deterministic algorithm is a policy on a one-point seed space. Rounds are indexed $0,\dots,T-1$.
--
--   Differences from the source:
--   - encoding: "any deterministic algorithm" (with the two bits of Theorem 7.1's proof) → a two-bit policy on the one-point seed space with the Dirac seed law; reason: the same algorithms
--   - reading: $I_j$, a piece of a partition of $[1/4,1/2]$ with unspecified endpoints → $I_j=(a_j,a_j+w)$ open; reason: the open pieces are pairwise disjoint, as a partition's are (the proof of Theorem 7.1 uses $\sum_j\mathbb E^0[N_j]\le T$); $S_j=S_0$ at the endpoints, so a query there carries no information and the proof is unchanged
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 3.6, p.51 (PDF 53), proof pp.51–52 (PDF 53–54); first stated p.16 (PDF 18)

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic

namespace BilateralProfitLB

open MeasureTheory

/-- **Claim 3.6**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.16
(PDF 18), restated with its proof pp.51–52 (PDF 53–54): for any deterministic algorithm with
two-bit feedback, `N_j` the number of rounds in which it posts a buyer price in `I_j`,
`E^j[N_j] − E^0[N_j] ≤ T/(22K²) · √(E^0[N_j])`.

Stated for every `K ≥ 1`, `j ∈ {1, …, K}`, horizon `T` and deterministic two-bit policy `π`;
`E^j` is the expectation of the run when the valuations are i.i.d. `𝒟_j`, `E^0` under `𝒟_0`.

**Formalization Note.** A deterministic algorithm is a policy on the one-point seed space `Unit`
with `P = dirac ()`; its prices are functions of the past feedback pairs
`(1{s_τ ≤ p_τ}, 1{q_τ ≤ b_τ})` (Theorem 7.1's proof, p.49). Rounds are `0, …, T − 1`. -/
theorem claim_3_6 (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (T : ℕ)
    (π : Policy Unit) :
    expCount π (Measure.dirac ()) (law K j) T (I K j) -
        expCount π (Measure.dirac ()) (law K 0) T (I K j) ≤
      (T : ℝ) / (22 * (K : ℝ) ^ 2) *
        Real.sqrt (expCount π (Measure.dirac ()) (law K 0) T (I K j)) := by sorry

end BilateralProfitLB
