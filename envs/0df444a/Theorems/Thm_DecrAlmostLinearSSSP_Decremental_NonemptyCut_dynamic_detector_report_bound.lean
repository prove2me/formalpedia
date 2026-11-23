-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_dynamic_detector_report_bound
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_detector_report_bound
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:16:43.217699+00:00
-- url     : https://prove2.me/theorems/b1749601-3ef3-4ab5-aa86-e9d8a92e4cd4
-- title:
--   Dynamic detector reports telescope to at most $T/\xi$
-- statement:
--   Consider a finite trace of the dynamic-cut protocol on a physical graph with $n$ vertices and $k$ edge identifiers. Active capacities are nonnegative and the detector threshold is $\xi>0$. Initially every active edge baseline equals its current unweighted endpoint-potential difference. Every legal insertion, deletion, paired demand change, ratio request, toggle and potential query updates the physical state according to the protocol.
--
--   On a toggle by $\tau$, the current cut $C$ satisfies $\operatorname{cap}_u(C)\le U$ and $0\le\tau\le U^{-1}$, and the potentials change by $y\mapsto y+\tau\mathbf1_C$. The reported identifiers form precisely the set of active edges satisfying
--
--   $$
--   \xi\le \left|u_e\big((y'_a-y'_b)-b_e\big)\right|,
--   $$
--
--   and exactly those baselines are reset to $y'_a-y'_b$. An insertion calibrates the inserted edge's baseline to its current endpoint difference. Non-toggle operations emit no reports, and their remaining baseline and potential changes follow the protocol.
--
--   If $R$ is the total number of reported identifiers, counted without duplicates within each finite report set, and $T$ is the number of toggles in the trace, then
--
--   $$
--   R\le \frac{T}{\xi}.
--   $$
--
--   This is the detector-report accounting used by Lemma 3.2: it permits the report factor $\Gamma=1$ and handles insertions and deletions directly, rather than only a fixed physical graph.
--
--   **Formalization Note** The trace is indexed by natural numbers and truncated at an arbitrary finite length. The right-hand sum is the real-valued number of toggle operations among the first $T$ transitions. Loops, parallel identifiers, zero toggles and empty traces are included.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2, ToggleCut and detector-report clauses; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. This formalizes the lemma's global report bound for the mission's legal dynamic physical traces.

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_toggle_detector_variation

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

open DecrAlmostLinearSSSP.Decremental

/-- Duplicate-free detector reports in a dynamic physical trace telescope to at most the
number of toggles divided by the threshold. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_detector_report_bound {n k : ℕ}
    (s : ℕ → CutState n k) (op : ℕ → CutOp n k)
    (report : ℕ → Finset (Fin k)) (xi : ℝ) (T : ℕ)
    (hu : ∀ t ≤ T, ∀ e ∈ (s t).physical.active, 0 ≤ (s t).physical.u e)
    (hxi : 0 < xi)
    (hinit : ∀ e ∈ (s 0).physical.active,
      (s 0).baseline e = (s 0).y ((s 0).physical.graph.tail e) -
        (s 0).y ((s 0).physical.graph.head e))
    (hphysical : ∀ t < T,
      (s (t + 1)).physical = applyPhysical (s t).physical (op t))
    (hvalid : ∀ t < T, CutOp.Valid (s t) (op t))
    (hcap : ∀ t < T, ∀ tau, op t = .toggle tau →
      cutCapacity (s t).physical (s t).lastCut ≤ (s t).lastU)
    (htau0 : ∀ t < T, ∀ tau, op t = .toggle tau → 0 ≤ tau)
    (htauU : ∀ t < T, ∀ tau, op t = .toggle tau → tau ≤ 1 / (s t).lastU)
    (hy : ∀ t < T, ∀ v, (s (t + 1)).y v = match op t with
      | .toggle tau => (s t).y v + if v ∈ (s t).lastCut then tau else 0
      | _ => (s t).y v)
    (hreport : ∀ t < T, report t = match op t with
      | .toggle _ => (s t).physical.active.filter (fun e =>
          xi ≤ |(s t).physical.u e *
            ((s (t + 1)).y ((s t).physical.graph.tail e) -
              (s (t + 1)).y ((s t).physical.graph.head e) - (s t).baseline e)|)
      | _ => ∅)
    (hb : ∀ t < T, ∀ e, (s (t + 1)).baseline e = match op t with
      | .toggle _ => if e ∈ report t then
          (s (t + 1)).y ((s t).physical.graph.tail e) -
            (s (t + 1)).y ((s t).physical.graph.head e)
        else (s t).baseline e
      | .insert f a b _ => if e = f then (s t).y a - (s t).y b else (s t).baseline e
      | _ => (s t).baseline e) :
    ((∑ t ∈ Finset.range T, (report t).card : ℕ) : ℝ) ≤
      (∑ t ∈ Finset.range T, (match op t with
        | .toggle _ => (1 : ℝ) | _ => 0)) / xi := by sorry
