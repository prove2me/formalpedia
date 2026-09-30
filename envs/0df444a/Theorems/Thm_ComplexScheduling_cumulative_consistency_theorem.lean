-- Prove2me | Theorems.Thm_ComplexScheduling_cumulative_consistency_theorem
-- name    : ComplexScheduling.cumulative_consistency_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:21:30.259958+00:00
-- url     : https://prove2.me/theorems/39c25bde-4048-4aac-8070-a2d7f414a5c9
-- title:
--   Theorem 3.8 — the interval consistency theorem for a cumulative resource
-- statement:
--   Consider an RCPSP instance with time windows $[r_i,d_i]$ and a renewable resource $k$ of
--   capacity $R_k$; let $I_k$ be the activities that need resource $k$, $w_i=r_{ik}p_i$ their work
--   and $W(J)=\sum_{i\in J}w_i$. Let $J\subseteq I_k$ and let $J',J''$ be proper subsets of $J$. If
--
--   $$
--   R_k\Bigl(\max_{\mu\in J\setminus J''}d_\mu\;-\;\min_{\nu\in J\setminus J'}r_\nu\Bigr)\;<\;W(J) ,
--   \tag{3.145}
--   $$
--
--   then in every feasible schedule (feasible for the RCPSP and within the windows) an activity
--   from $J'$ starts first in $J$ or an activity from $J''$ ends last in $J$.
--
--   This is Theorem 3.8, the cumulative counterpart of Theorem 3.7: instead of "the activities of
--   $J$ cannot overlap" the argument uses "the resource supplies at most $R_k$ units per time unit",
--   so an interval of length $L$ offers $R_kL$ units of work, and if the activities of $J$ were all
--   processed between the earliest head of $J\setminus J'$ and the latest deadline of
--   $J\setminus J''$ they would have less than $W(J)$ available.
--
--   **Formalization Note** The condition is the family $R_kd_\mu<R_kr_\nu+W(J)$ over
--   $\nu\in J\setminus J'$, $\mu\in J\setminus J''$, equivalent to (3.145) and free of subtraction.
--   Unlike Theorem 3.7 the book imposes no $\nu\ne\mu$ here, and the theorem has no hypothesis
--   $J'\cup J''\ne\emptyset$: with $J'=J''=\emptyset$ the conclusion is false and the theorem says
--   that no feasible schedule exists, which is the cumulative infeasibility test. "Starts first" is
--   read with $\le$, so a tie for the earliest start counts, which is what the book's proof uses
--   when several activities of a cumulative resource start together. $J\subseteq I_k$ is the
--   hypothesis that every activity of $J$ has positive demand for $k$.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.5, printed p. 186 (PDF p. 196), Theorem 3.8: "Let J′, J′′ ⊂ J ⊆ I_k. If R_k · max_{ν∈J\J′, μ∈J\J′′} (d_μ − r_ν) = R_k · (max_{μ∈J\J′′} d_μ − min_{ν∈J\J′} r_ν) < W(J), (3.145) then in J an activity from J′ must start first or an activity from J′′ must end last."

import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem cumulative_consistency_theorem {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (k : Fin r) (J J' J'' : Finset (Fin n)) (hJk : ∀ i ∈ J, 0 < demand i k)
    (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'',
      Rcap k * dl μ < Rcap k * rel ν + totalWork p demand k J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by sorry
end ComplexScheduling
