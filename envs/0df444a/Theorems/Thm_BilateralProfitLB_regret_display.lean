-- Prove2me | Theorems.Thm_BilateralProfitLB_regret_display
-- name    : BilateralProfitLB.regret_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:19.051836+00:00
-- url     : https://prove2.me/theorems/d4452858-4c74-4e28-880b-e98b89f039a0
-- title:
--   §7, p.52 — the regret against $\mathcal D_j$ is at least $(T-\mathbb E^j[N_j])\Delta$
-- statement:
--   Let $K\ge1$, $j\in\{1,\dots,K\}$, $T\ge0$, and let $\mathcal A$ be any posted-price policy with two-bit feedback, possibly randomized through a seed drawn from a probability space $(\Omega,P)$. Let $N_j$ be the number of rounds with buyer price $q_t\in I_j$ and $\mathbb E^j$ the expectation when the valuations are i.i.d. $\mathcal D_j$, independent of the seed. Then the regret of $\mathcal A$ against $\mathcal D_j$ satisfies
--   $$R_T(\mathcal A,\mathcal D_j)\ge\big(T-\mathbb E^j[N_j]\big)\Delta,\qquad \Delta=\frac{w^2}{384\cdot12},$$
--   witnessed by a single comparator: there is $(p,q)\in[0,1]^2$ with $\sum_{t=1}^T\big(\mathbb E^j[\mathrm{Profit}_t(p,q)]-\mathbb E^j[\mathrm{Profit}_t(p_t,q_t)]\big)\ge(T-\mathbb E^j[N_j])\Delta$.
--
--   Each round spent outside the right interval costs at least the gap $\Delta$; together with Claim 3.6 this gives Theorem 7.1.
--
--   **Formalization Note** The comparator is not fixed to $(q^\star_j/2,q^\star_j)$, since $q^\star_j$ need not maximize $h^j$ inside $I_j$.
--
--   Differences from the source:
--   - generalization: "the deterministic algorithm $\mathcal A$" → every, possibly randomized, two-bit policy on a probability space of seeds; reason: a deterministic algorithm is the case of a one-point seed space, and the same argument applies round by round
--   - encoding: $R_T=\sup_{(p,q)\in[0,1]^2}\sum_t(\dots)\ge(T-\mathbb E^j[N_j])\Delta$ → some comparator $(p,q)\in[0,1]^2$ achieves the bound; reason: the supremum is attained (p.4), so the two agree
--   - reading: $N_j$ counts buyer prices in $I_j$, a piece of a partition with unspecified endpoints → $I_j=(a_j,a_j+w)$ open; reason: the strongest choice: fewer rounds are counted, so the bound implies the one for every choice of endpoints
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §7, p.52 (PDF 54), display after the proof of Claim 3.6; also p.16 (PDF 18)

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic

namespace BilateralProfitLB

open MeasureTheory

/-- **§7, p.52 (PDF 54), display after Claim 3.6's proof**, Brüstle, di Gregorio, Fusco,
Leonardi (manuscript, sha256 e91e8127…): "By Claim 3.4 and recalling that `∆ = w²/(384·12)` is
the 'suboptimality gap' of playing outside the right interval, the regret of the deterministic
algorithm `𝒜` against the generic distribution `𝒟_j` is `R_T(𝒜, 𝒟_j) ≥ (T − E^j[N_j])∆`".

Stated for every `K ≥ 1`, `j ∈ {1, …, K}`, horizon `T` and every (possibly randomized) two-bit
policy `π` on a probability space `(Ω, P)`: some comparator `(p, q) ∈ [0, 1]²` has
`Σ_t (E^j[Profit_t(p, q)] − E^j[Profit_t(p_t, q_t)]) ≥ (T − E^j[N_j]) ∆`.

**Formalization Note.** The paper's `R_T` is the supremum over comparators; a comparator that
achieves the bound is the same statement (the supremum is attained, p.4). The comparator is not
fixed to `(q⋆_j/2, q⋆_j)`: `q⋆_j` need not maximize `h^j` on `I_j`. -/
theorem regret_display (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (T : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (π : Policy Ω) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ((T : ℝ) - expCount π P (law K j) T (I K j)) * Delta K ≤ regret π P (law K j) T a := by sorry

end BilateralProfitLB
