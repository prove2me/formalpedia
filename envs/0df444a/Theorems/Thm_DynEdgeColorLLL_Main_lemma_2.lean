-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_2
-- name    : DynEdgeColorLLL.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:29.784288+00:00
-- url     : https://prove2.me/theorems/d063963f-fa85-4bc6-ae52-14b72839c42b
-- title:
--   Lemma 2 ([CPS14], App. B) — witness-tree tail $(q/4d^2)^r\,x(C)/(1-x(C))$
-- statement:
--   Fix a finite set of variables with laws $D_x$, a truth-table family on clauses with IDs in $[m]$, and an instance $\mathrm{vbl}$ satisfying the standing assumptions of §3.1: uniform parameters $k,s\ge1$, $d\ge2$, $q\in(0,1/2)$, and assumption (1) with a function $x:[m]\to[0,1)$ satisfying $x(C)/(1-x(C))\le K$. Run the static parallel resampling algorithm of [CPS14] on independent randomness tables $R(x,i)\sim D_x$.
--
--   Let $C$ be a clause and $r\ge1$. "The execution contains a 2-witness tree with root label $C$ and at least $r$ nodes" means that some resampling event $(r',C)$ of the log has a 2-witness tree (Definition 1) with at least $r$ nodes. Then
--   $$\Pr\bigl[\text{the execution contains a 2-witness tree with root label }C\text{ and at least }r\text{ nodes}\bigr]\le\Bigl(\frac{q}{4d^2}\Bigr)^r\frac{x(C)}{1-x(C)}.$$
--
--   This is the probabilistic core of the [CPS14] analysis. With Lemma 1 it gives almost-sure termination and the tail bounds of Lemma 3 and Corollary 1.
--
--   **Formalization Note.** The node count of the 2-witness tree is the number of log entries joined to the root entry by a chain in which each label lies in the closed 2-ball of the next. This is exactly the node set Definition 1 builds, whatever the tie-breaking among deepest nodes.
--
--   Differences from the source:
--   - encoding: a set V of variables and clause IDs in [m] → a finite type of variables and clause IDs Fin m; reason: every instance in the paper is finite at every moment
--   - encoding: the probability of an event → the measure of the event set under the product law of the tables (an outer measure, so the bound needs no measurability side condition); reason: for measurable events this is the probability; for a non-measurable set the outer measure is an upper bound on any reading
--   - encoding: Definition 1 builds a rooted tree, attaching each node to any deepest eligible node → the number of nodes is the number of log entries joined to the root entry by a witness chain; reason: the set of indices Definition 1 adds does not depend on the tie-breaking, and the statement uses only the number of nodes
--   - encoding: a truth table f_{C,U} : ∏_{x∈U} Ω_x → {0,1} for each clause C and variable set U → a predicate f C U on full assignments that depends only on the coordinates in U, is false for U = ∅, and has a measurable falsifying set (IsTruthTableFamily); reason: the same truth tables; the empty-clause convention is stated in §3.1, and measurability is presupposed by Pr[C] in assumption (1)
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 2 ([CPS14], Appendix B), printed p. 11 (PDF p. 13); standing assumptions §3.1, printed pp. 9–10 (PDF pp. 11–12); Definition 1, printed p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

/-- Lemma 2 ([CPS14], Appendix B; Peng–Ghaffari, STOC 2027 submission #615, printed p. 11,
PDF p. 13). Under the standing assumptions of §3.1 (parameters `k, s, d`, `q ∈ (0, 1/2)` and
assumption (1) with the function `xw`), for every clause `C` and `r ≥ 1` the probability that the
execution of the parallel resampling algorithm contains a 2-witness tree with root label `C` and
at least `r` nodes is at most `(q/4d²)^r xw(C)/(1 − xw(C))`. -/
theorem lemma_2 {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*}
    [∀ x, MeasurableSpace (Ω x)] (D : (x : X) → Measure (Ω x)) [∀ x, IsProbabilityMeasure (D x)]
    {m : ℕ} (f : TruthTables X Ω m) (vbl : Fin m → Finset X) (k s d : ℕ) (q K : ℝ)
    (xw : Fin m → ℝ) (hf : IsTruthTableFamily f) (hpar : HasParams vbl k s d)
    (hq : 0 < q ∧ q < 1 / 2) (h1 : Assumption1 D f vbl d q K xw)
    (C : Fin m) (r : ℕ) (hr : 1 ≤ r) :
    tableMeasure D {τ | HasWitnessTree f vbl τ C r} ≤
      ENNReal.ofReal ((q / (4 * (d : ℝ) ^ 2)) ^ r * (xw C / (1 - xw C))) := by sorry

end DynEdgeColorLLL.Main
