-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Supplement_lemma_4_1
-- name    : DecrAlmostLinearSSSP.Decremental.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:17:46.362971+00:00
-- url     : https://prove2.me/theorems/f9fd52d7-92cc-4038-9fb0-164da7b83ad3
-- title:
--   Lemma 4.1 — Initially empty polynomial-weight incremental distances
-- statement:
--   Fix a polynomial-weight exponent $c\in\mathbb N$. There are one deterministic scalar arithmetic program, constants $C>0$ and $Q\in\mathbb N_{>0}$, and a positive subpolynomial function $a$, chosen before all instances, with the following property. Let $m\ge n\ge2$, let $W\ge1$ be real with $W\le m^c$, and let $1/m<\epsilon<1$. Start with an empty directed graph on $n$ vertices, fix $s$, and insert at most $m$ original edges of integral weights in $[1,W]$. All calls terminate, and at initialization and after every completed insertion every vertex simultaneously has an explicit estimate satisfying
--
--   $$
--   d_t(v)\le D_t(v)\le(1+\epsilon)d_t(v),\qquad
--   T_{\mathrm{maintenance}}\le C m a(m)\epsilon^{-1}.
--   $$
--
--   Infinity flags detect unreachability exactly, and distance and flag queries cost at most $Q$ scalar operations. The size bound covers all original edge identifiers; the program sees each edge only when it is inserted. No reachability or incoming-source restriction is imposed.
--
--   This is the distance-estimation support for the incremental companion theorem. For the proof accounting, let $T$ count successful augmentations, let $J$ count threshold transactions, and let $B$ be the potential budget. The normalization parameters are $H_0=4nW$ and $Q_0=8nH_0$. The cycle quality factor is $K\ge2^{20}$, the amplification $A$ is the least power of four at least $2^{12}\lceil\log_2m\rceil/\epsilon$, and $M=mAQ_0K$. The clipping threshold and transaction ratio are $\kappa=M^{-20}$ and $\tau=\epsilon/64$. The proof gives $B=100mA\log M$, $T\le4BK^6$ and $J\le mA\log M/64$. These are proof parameters on pp.18, 28–31, not assumed algorithmic invariants; the final statement retains a uniform subpolynomial overhead rather than inventing an external cycle-implementation constant.
--
--   **Formalization Note** Integrality is imposed only on this statement and Theorem 1.2. The graph and machine primitives are the two published base definitions. The program and all operation constants may depend on the fixed exponent $c$, and on no individual graph or accuracy.
--
--   Differences from the source:
--   - encoding: finite directed graph with original positive edge weights and active insertion prefixes → Fin-indexed original edge identifiers with legal disjoint initial and insertion lists and extended nonnegative walk distance; reason: preserves all finite directed instances including parallel edges and entering-source edges; finite weights are embedded in ENNReal and empty feasible walk sets have distance infinity
--   - encoding: deterministic unit-cost data structure with explicit maintained entries and query operations → one finite scalar arithmetic program with prefix-only input, actual terminating executions, explicit memory cells, preserved query memory and charged input delivery; reason: fixes the execution and array layout without assuming correctness, termination or a fast implementation; uniform constants absorb the fixed 32-unit interface charges
--   - encoding: m^(1+o(1)) times the displayed accuracy and weight factors → C m a(m) times the same factors, with a positive and log(a(m))/log(max(2,m)) tending to zero; reason: makes the asymptotic overhead uniform before graph, accuracy, W and streams; only the fixed polynomial-weight exponent may affect constants in Lemma 4.1
--   - encoding: W=m^O(1) → for every fixed natural exponent c, W≤m^c, with program and constants selected after c and before instances; reason: every fixed polynomial weight bound is covered by enlarging its exponent; no uniformity across fixed polynomial exponents is asserted
--   - encoding: positive integer edge lengths in [1,W] → integer edge lengths with a real numerical upper bound W≥1; reason: integrality applies to the edge lengths, not to the bound; no integer-cap hypothesis is added
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p.18, Lemma 4.1; pp.21, 30–31, query contract and (4.33)–(4.35)

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Guarantees

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- Lemma 4.1, p.18, with the completed-state and explicit-write interpretation of pp.21,30–31.
The fixed polynomial weight exponent may affect the program and overhead; no instance may.
No incremental IPM invariants or efficient external implementation are assumed as hypotheses. -/
theorem lemma_4_1 :
    ∀ c : ℕ, ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (Q : ℕ),
      0 < C ∧ Subpolynomial a ∧ 0 < Q ∧
      ∀ i : Instance, i.Valid → i.Integral → 2 ≤ i.n → i.initial = [] →
        i.W ≤ (i.size : ℝ) ^ c → 1 / (i.size : ℝ) < i.accuracy → i.accuracy < 1 →
        ∀ es : List (Fin i.k), i.Legal es → ∃ cs : List Machine,
          Run p i (fun _ => []) es cs ∧
          DistanceStates p i es cs (1 + i.accuracy) Q ∧
          WithinBudget i (fun _ => []) es cs (almostLinearBudget C a i false) := by sorry

end DecrAlmostLinearSSSP.Decremental.Supplement
