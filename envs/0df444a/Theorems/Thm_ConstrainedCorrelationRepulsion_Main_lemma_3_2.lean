-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_3_2
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:33.956369+00:00
-- url     : https://prove2.me/theorems/13aa6f3f-f74d-4a41-9e19-6874b27c1d55
-- title:
--   Lemma 3.2 — must-link averaging and deterministic projection
-- statement:
--   Given any feasible unweighted constrained instance $I$, the specified same-vertex true-twin construction produces a complementary probability-cost instance $J$ with no must-links and $\mathrm{OPT}(J)\le\mathrm{OPT}(I)$. For every feasible partition $Q$ of $J$, the deterministic constructive gathering routine returns a feasible partition $P$ of $I$ with
--
--   $$
--   \mathrm{cost}_I(P)-\mathrm{cost}_J(Q)\le\mathrm{OPT}(I)-\mathrm{OPT}(J).
--   $$
--
--   Both construction and projection have uniform polynomial-time implementations. The optimum difference equals the fixed internal-negative and incompatible-positive cost in (7), and the output costs lie in $[0,1]$ and sum to one per pair.
--
--   **Formalization Note.** The gather routine performs $n^2+1$ steps, with idle steps once every class is intact; the proof on printed p.15 bounds the improving steps by $\binom n2$.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - encoding: pair costs defined only for distinct vertices → total functions on Sym2 with unused diagonal padding; probability padding lies in [0,1]; reason: every source assignment extends to such a function, every objective ignores the diagonal, and no source instance is excluded
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 3.2 and equations (7)–(8), printed pp.14–15 (PDF pp.15–16)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Reductions
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_3_2 :
  ∃ buildCode projectCode : Program, Deterministic buildCode ∧ Deterministic projectCode ∧
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ n (I : Instance n), FeasibleInput I →
      let J := twinInstance I
      let w := twinCosts I
      let B := polynomialBound C d n
      (∀ e, 0 ≤ w.separate e ∧ w.separate e ≤ 1 ∧ w.together e = 1 - w.separate e) ∧
      J.mustLink = ⊥ ∧ FeasibleInput J ∧ weightedOPT J w ≤ (OPT I : ℝ) ∧
      (OPT I : ℝ) - weightedOPT J w = twinFixedCost I ∧
      BoundedRun true buildCode (inputOracle I) (initialState n) B ∧
      (∀ st ∈ (machineRun true buildCode (inputOracle I) (initialState n) B).support,
        ∀ u v, st.realMem (u.val*n + v.val) = twinProbability I u v ∧
          (st.natMem (u.val*n + v.val) = 1 ↔ J.cannotLink.Adj u v)) ∧
      (∀ Q, Feasible J Q →
        BoundedRun true projectCode (inputOracle I) (projectionInitial Q) B ∧
        outputLaw projectCode (inputOracle I) (projectionInitial Q) B = PMF.pure (gather I Q) ∧
        Feasible I (gather I Q) ∧
        (cost I (gather I Q) : ℝ) - weightedCost w Q ≤ (OPT I : ℝ) - weightedOPT J w) := by sorry

end ConstrainedCorrelationRepulsion.Main
