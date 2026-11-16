-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_claim_6_3
-- name    : CorrKClust.BalancedPivot.Supplement.claim_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:57.77136+00:00
-- url     : https://prove2.me/theorems/7875b0cd-e32e-4286-9648-18c0dfbfd4b8
-- title:
--   Claim 6.3 — four consequences of the common good event
-- statement:
--   In the Section 6 disjoint-clique setup, let $n\ge2$, $\ell>k\ge1$, $c_0>0$, $c_1=\max\{40,2c_0+1\}$, and $0\le i\le\lfloor\log_2n\rfloor$. Put $B_i=c_1n\log_2n/2^i$ and $T_i=\{2^i\le T_0<2^{i+1}\}$. On the simultaneous large-clique event $G_1$ intersected with $T_i$, all four conclusions hold:
--   $$\begin{gathered}
--   |K|<B_i\ \text{for every leading clique of a cluster in }S,\\
--   |K|<B_i\ \text{for every original clique }K\subseteq U,\\
--   m\le Y_i,\qquad W\le s(G)+B_iY_i,\\
--   N_i\ge k-r(G).
--   \end{gathered}$$
--   Here $S$ uses the threshold $c_0\log_2n$ at $T_0$, $U$ is the uncovered set, $W=|U|$, and $m$ counts top-$k$ cliques wholly in $U$. The counts $Y_i,N_i$ are from the fixed tails after $k$ and $r$, at capped deterministic time $\min\{2^{i+1},n\}$. The claim uses one common event and makes no independence assertion.
--
--   Differences from the source:
--   - encoding: size-ordered cliques and the events G1 and Ti of Section 6 → deterministically sorted nonempty blocks, base uncovered at T0, and capped fixed-set counts; all four conclusions conjoined; reason: ties may be ordered arbitrarily; all sets and times agree with the source and no conditioning is replaced by independence
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Claim 6.3, p. 26

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Uniform

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Claim 6.3, printed p.26: all four clauses on the same G1∩Ti, with c0 free. -/
theorem claim_6_3 (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    (G : SimpleGraph (Fin n)) (Q : Fin n → Fin n) (hQ : IsCliquePartition G Q)
    (hℓ : k < (blocks Q).card) (c0 : ℝ) (hc0 : 0 < c0)
    (i : ℕ) (hi : i ≤ Nat.log 2 n) (σ : ArrivalOrder (Fin n))
    (hgood : goodOne Q c0 σ) (hinterval : interval G k i σ) :
    (∀ v ∈ smallPivots G k σ (c0 * logTwo n),
      (finalSize G σ v : ℝ) < dyadicB n c0 i) ∧
    (∀ K ∈ blocks Q, K ⊆ uncovered G σ (kthPivotTime G k σ) →
      (K.card : ℝ) < dyadicB n c0 i) ∧
    (missingTop G Q k σ ≤ countY Q k i σ ∧
      ((uncovered G σ (kthPivotTime G k σ)).card : ℝ) ≤
        (cliqueS (blockSizes Q) k : ℝ) + dyadicB n c0 i * countY Q k i σ) ∧
    k - cliqueR (blockSizes Q) k ≤ countN Q k i σ := by sorry

end CorrKClust.BalancedPivot.Supplement
