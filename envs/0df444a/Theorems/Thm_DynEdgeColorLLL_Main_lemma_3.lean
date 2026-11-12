-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_3
-- name    : DynEdgeColorLLL.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:23.831349+00:00
-- url     : https://prove2.me/theorems/77e74b3f-e2c7-4d75-9b08-be140307d521
-- title:
--   Lemma 3 — $\Pr[b_{x,r}=1]\le\Pr[r_x\ge r]=O(k(q/4d^2)^r)$
-- statement:
--   Fix a finite set of variables with laws $D_x$, a truth-table family on clauses with IDs in $[m]$, and an instance $\mathrm{vbl}$ satisfying the standing assumptions of §3.1: uniform parameters $k,s\ge1$, $d\ge2$, $q\in(0,1/2)$, and assumption (1) with a function $x:[m]\to[0,1)$ satisfying $x(C)/(1-x(C))\le K$. Run the static parallel resampling algorithm of [CPS14] on independent randomness tables $R(x,i)\sim D_x$.
--
--   For every variable $x$ and every stage $r\ge1$,
--   $$\Pr[b_{x,r}=1]\le\Pr[r_x\ge r]\le C\,K\,k\Bigl(\frac{q}{4d^2}\Bigr)^r ,$$
--   where $C$ is an absolute constant, $b_{x,r}$ records whether $x$ is resampled at stage $r$, and $r_x$ is the last stage at which $x$ is resampled.
--
--   The tail bound shows that late resamplings are rare. It is what makes the dynamic maintenance of the transcript cheap.
--
--   **Formalization Note.** $r_x$ takes values in $\mathbb N\cup\{\infty\}$ ($\infty$ if $x$ is resampled infinitely often), and the $O(\cdot)$ is the explicit $C\,K$ with $C$ absolute.
--
--   Differences from the source:
--   - reading: O(k(q/4d²)^r) → C·K·k·(q/4d²)^r with C absolute and K the bound on max x(C)/(1−x(C)) of assumption (1); reason: assumption (1) states max x/(1−x) = O(1); the O hides that constant and nothing else
--   - generalization: the convention "we may take k ≤ d" (PDF p. 11) → k ≤ d is not assumed; reason: the bound then holds a fortiori for k ≤ d
--   - encoding: a set V of variables and clause IDs in [m] → a finite type of variables and clause IDs Fin m; reason: every instance in the paper is finite at every moment
--   - encoding: the probability of an event → the measure of the event set under the product law of the tables (an outer measure, so the bound needs no measurability side condition); reason: for measurable events this is the probability; for a non-measurable set the outer measure is an upper bound on any reading
--   - encoding: r_x = max({0} ∪ {r : b_{x,r} = 1}) → r_x as a supremum in ℕ∞; reason: the same value whenever the set is finite; ⊤ on the null event of infinitely many resamplings
--   - encoding: a truth table f_{C,U} : ∏_{x∈U} Ω_x → {0,1} for each clause C and variable set U → a predicate f C U on full assignments that depends only on the coordinates in U, is false for U = ∅, and has a measurable falsifying set (IsTruthTableFamily); reason: the same truth tables; the empty-clause convention is stated in §3.1, and measurability is presupposed by Pr[C] in assumption (1)
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 3, printed p. 11 (PDF p. 13); standing assumptions §3.1, printed pp. 9–10 (PDF pp. 11–12); Table 1, printed p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

/-- Lemma 3 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 11, PDF p. 13). Under the
standing assumptions of §3.1, for every variable `x` and `r ≥ 1`,
`Pr[b_{x,r} = 1] ≤ Pr[r_x ≥ r] = O(k (q/4d²)^r)`; the `O` hides an absolute constant times the
bound `K` on `max xw/(1 − xw)` of assumption (1). -/
theorem lemma_3 :
    ∃ Cabs : ℝ, ∀ {X : Type} [Fintype X] [DecidableEq X] {Ω : X → Type}
      [∀ x, MeasurableSpace (Ω x)] (D : (x : X) → Measure (Ω x))
      [∀ x, IsProbabilityMeasure (D x)] {m : ℕ} (f : TruthTables X Ω m)
      (vbl : Fin m → Finset X) (k s d : ℕ) (q K : ℝ) (xw : Fin m → ℝ),
      IsTruthTableFamily f → HasParams vbl k s d → (0 < q ∧ q < 1 / 2) →
      Assumption1 D f vbl d q K xw →
      ∀ (x : X) (r : ℕ), 1 ≤ r →
        tableMeasure D {τ | bx f vbl τ x r} ≤ tableMeasure D {τ | (r : ℕ∞) ≤ rx f vbl τ x} ∧
        tableMeasure D {τ | (r : ℕ∞) ≤ rx f vbl τ x} ≤
          ENNReal.ofReal (Cabs * K * k * (q / (4 * (d : ℝ) ^ 2)) ^ r) := by sorry

end DynEdgeColorLLL.Main
