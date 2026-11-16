-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_lemma_6_1
-- name    : CorrKClust.BalancedPivot.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:53.693459+00:00
-- url     : https://prove2.me/theorems/882b0203-7654-403a-94ca-f3020859fb38
-- title:
--   Lemma 6.1 — strict early-count lower tail
-- statement:
--   Fix a graph size $n$ and a deterministic time $1\le t\le n$. Let $c_1>0$ and let $K$ be any fixed subset of vertices with $|K|\ge c_1n\log_2n/t$. Under the uniform arrival permutation,
--   $$\Pr\left[|K\cap V_{\le t}|>\tfrac12c_1\log_2n\right]\ge1-n^{-c_1/8}.$$
--   In particular this holds for every clique of the source size. The subset and time are fixed before sampling; the inequality for the count is strict. The result supplies the later simultaneous good event by a union bound.
--
--   Differences from the source:
--   - generalization: a fixed clique → any fixed subset of the vertex set; reason: the hypergeometric proof uses only cardinality; every clique is such a subset
--   - encoding: any time t → integer sample size 1≤t≤n, with uniform finite permutation probability; reason: this is the legal arrival-time range; t=0 would make the displayed size threshold undefined
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 6.1, p. 23

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Uniform

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Lemma 6.1, printed p.23. Generalized to a fixed subset: adjacency is unused.
The strict prefix-count inequality and exact exponent are retained. -/
theorem lemma_6_1 (n t : ℕ) (ht : 0 < t) (htn : t ≤ n)
    (c1 : ℝ) (hc1 : 0 < c1) (K : Finset (Fin n))
    (hK : c1 * n * logTwo n / t ≤ (K.card : ℝ)) :
    1 - (n : ℝ) ^ (-c1 / 8) ≤
      probability (fun σ : ArrivalOrder (Fin n) =>
        (c1 / 2) * logTwo n < (prefixCount K t σ : ℝ)) := by sorry

end CorrKClust.BalancedPivot.Supplement
