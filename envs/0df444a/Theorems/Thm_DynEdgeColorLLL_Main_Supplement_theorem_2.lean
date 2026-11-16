-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_Supplement_theorem_2
-- name    : DynEdgeColorLLL.Main.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:57.715628+00:00
-- url     : https://prove2.me/theorems/c9532159-619f-40b9-8193-f38515f8480b
-- title:
--   Theorem 2 — dynamic LLL with all three updates, primitive costs and recourse
-- statement:
--   There is one finite randomized oracle RAM program and positive absolute constants $C_{\rm ins},C_{\rm del},C_{\rm time},C_{\rm rec}$ with the following guarantees for every §3.1 instance family and every correct implementation of its sampling, evaluation and clause-update interfaces.
--
--   Variables have arbitrary domains $\Omega_x$ and independent laws $D_x$; the fixed labelled clauses are initially empty and satisfied. Uniform parameters bound variable occurrences by $k\ge1$, clause sizes by $s\ge1$, and closed dependency neighbourhoods by $d\ge2$, with $k\le d$. Fix $0<q<1/2$ and a finite bound $K_0\ge0$ on every witness ratio $x(C)/(1-x(C))$. Assumption (1), with its closed two-hop product, holds at every operation boundary with some witness; witnesses may change between instances. Let $\overline K=\max(1,K_0)$. Primitive expected costs are finite time units, at least one, with $T_{\rm update}\le T_{\rm eval}$.
--
--   For every finite legal operation sequence fixed before the coins, the program completes and reports a satisfying assignment almost surely at every boundary. It supports:
--
--   1. Introducing an isolated variable in expected charged time at most $C_{\rm ins}T_{\rm sample}$.
--   2. Removing an isolated variable in at most $C_{\rm del}$ ordinary time whenever the preceding operation has completed.
--   3. Applying any batch $\mathcal B$ of distinct clause–live-variable incidence toggles, with
--
--   $$\mathbb E[\mathrm{time}(\mathcal B)]\le C_{\rm time}|\mathcal B|\bigl[T_{\rm update}+\overline K k^2s^2dq(T_{\rm eval}+T_{\rm sample})\bigr],$$
--
--   $$\mathbb E^*[\mathrm{recourse}(\mathcal B)]\le C_{\rm rec}\overline K|\mathcal B|s^2q.$$
--
--   Only the before/after instances of a batch must satisfy the LLL and parameter conditions. Recourse counts surviving variables whose reported final values change. Each cost is measurable, and each expectation is over the original persistent randomness for that particular operation, rather than an amortized average. The program reads parameters and the current operation as input, cannot inspect truth-table families, and pays for its own steps, argument preparation, primitive calls and output writes. Empty batches may be zero-work no-ops.
--
--   This is the general dynamic LLL companion theorem, including its oracle-cost interface, rather than a static existence or resampling-count bound.
--
--   Differences from the source:
--   - encoding: A dynamic variable set with arbitrary domains and laws and an oblivious update sequence → One fixed finite program handles all finite birth-ID sets, arbitrary measurable domains and laws, all primitive implementations and every finite history fixed before the coins; reason: Each finite history embeds by giving every birth a fresh ID; N and the history length have no a priori bound
--   - reading: The oracle costs and the O(1) bound on the witness ratios are uniform throughout the sequence → Positive absolute C_ins, C_del, C_time and C_rec precede all instance data; batch repair factors expose max(1,K_0) linearly; reason: These quantifiers give exactly the printed big-O bounds for each fixed O(1) witness bound; §3.4 counts primitives and geometric sums
--   - encoding: Each update has expected time, isolated removal takes ordinary O(1) time, and the algorithm maintains a satisfying assignment → Charged costs are measurable extended nonnegative quantities with infinity on divergence; output and completion hold almost surely; removal has a pointwise bound whenever its preceding operation completed; reason: An operation cannot be invoked on a tape on which a preceding operation diverged; no conditioning on an arbitrary previous output replaces the per-operation expectation
--   - generalization: Expected recourse counts changes in the final output → The upper expectation of the actual changed-output count satisfies the same bound; reason: It agrees with ordinary expectation for measurable recourse and extends the claim without adding measurable-diagonal or finite-domain hypotheses; the same resampling-bit majorant bounds it
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Theorem 2, printed p. 10 (PDF p. 12)

import Definitions.Def_DynEdgeColorLLL_Main_Supplement_DynamicLLL

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement

/-- Theorem 2, printed p. 10 / PDF p. 12. One finite program and absolute
constants, independent of all sizes, laws, implementations, parameters and histories. -/
theorem theorem_2 :
    ∃ (P : OracleRAM.Program) (C_ins C_del C_time C_rec : ℝ),
      0 < C_ins ∧ 0 < C_del ∧ 0 < C_time ∧ 0 < C_rec ∧
      DynamicGuarantee P C_ins C_del C_time C_rec := by sorry

end DynEdgeColorLLL.Main.Supplement
