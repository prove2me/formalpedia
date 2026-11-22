-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_finite_detector_report_bound
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.finite_detector_report_bound
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-22T23:10:15.874403+00:00
-- url     : https://prove2.me/theorems/b2c76571-d813-4d0d-92a8-db6054528ad3
-- title:
--   Finite detector reports telescope to at most $T/\xi$
-- statement:
--   Fix an oriented physical multigraph with nonnegative active capacities $u_e$ and a finite sequence of $T$ cut toggles. At step $t$, write $D_t(e)=y_{t,a}-y_{t,b}$ for the unweighted potential difference across edge $e=(a,b)$. The $t$-th toggle adds $\tau_t\mathbf1_{C_t}$ to the potentials, where
--
--   $$
--   0\le \tau_t\le U_t^{-1},\qquad \operatorname{cap}_u(C_t)\le U_t.
--   $$
--
--   The initial detector baseline is calibrated by $b_{0,e}=D_0(e)$. After each toggle, a duplicate-free scan reports exactly the active edges satisfying
--
--   $$
--   \left|u_e\bigl(D_{t+1}(e)-b_{t,e}\bigr)\right|\ge \xi,
--   $$
--
--   where $\xi>0$, and resets precisely those reported baselines to $D_{t+1}(e)$; every other baseline is unchanged. If $R_t$ is the number of reports at step $t$, then
--
--   $$
--   \sum_{t=0}^{T-1}R_t\le \frac{T}{\xi}.
--   $$
--
--   This is the finite-trace form of the report bound in the dynamic cut interface. It packages the baseline-reset and duplicate-free-scan hypotheses needed to charge every report against capacity-weighted detector variation. Edge insertions are outside this fixed-graph lemma: an implementation should start a new calibrated trace at each insertion, or extend the state model with per-edge lifetimes.
--
--   **Formalization Note** Each report set is a `Finset`, so duplicate-freeness is intrinsic. The initial-calibration hypothesis includes the interface's actual initialization $y=0$ and $b=0$ as a special case.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2, §3.2.1, ToggleCut and the bound of at most ΓT/ξ detector reports; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. This is the finite duplicate-free baseline-reset accounting argument for Γ=1, using the one-toggle variation bound proved in DecrAlmostLinearSSSP.Decremental.NonemptyCut.toggle_detector_variation.

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- A finite duplicate-free detector trace has at most `T / xi` reports. -/
theorem finite_detector_report_bound {n k : ℕ} (g : Physical n k)
    (y : ℕ → Fin n → ℝ) (b : ℕ → Fin k → ℝ)
    (C : ℕ → Finset (Fin n)) (tau U : ℕ → ℝ)
    (report : ℕ → Finset (Fin k)) (xi : ℝ) (T : ℕ)
    (hu : ∀ e ∈ g.active, 0 ≤ g.u e) (hxi : 0 < xi)
    (hinit : ∀ e, b 0 e = y 0 (g.graph.tail e) - y 0 (g.graph.head e))
    (hcap : ∀ t < T, cutCapacity g (C t) ≤ U t)
    (htau0 : ∀ t < T, 0 ≤ tau t)
    (htauU : ∀ t < T, tau t ≤ 1 / U t)
    (hy : ∀ t < T, ∀ v,
      y (t + 1) v = y t v + if v ∈ C t then tau t else 0)
    (hreport : ∀ t < T, report t = g.active.filter (fun e =>
      xi ≤ |g.u e * (y (t + 1) (g.graph.tail e) -
        y (t + 1) (g.graph.head e) - b t e)|))
    (hb : ∀ t < T, ∀ e, b (t + 1) e =
      if e ∈ report t then
        y (t + 1) (g.graph.tail e) - y (t + 1) (g.graph.head e)
      else b t e) :
    ((∑ t ∈ Finset.range T, (report t).card : ℕ) : ℝ) ≤ (T : ℝ) / xi := by sorry
