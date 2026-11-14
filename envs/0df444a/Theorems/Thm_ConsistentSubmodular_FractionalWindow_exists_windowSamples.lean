-- Prove2me | Theorems.Thm_ConsistentSubmodular_FractionalWindow_exists_windowSamples
-- name    : ConsistentSubmodular.FractionalWindow.exists_windowSamples
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:44.290198+00:00
-- url     : https://prove2.me/theorems/47e8790c-7e6f-46fe-aa3e-cb61ff332f88
-- title:
--   Existence of window samples for a fractional window
-- statement:
--   Let $W$ be a fractional window for $(f,\mathrm{old},Q,\kappa,N,T,\mathrm{initial},\mathrm{terminal},\alpha,S)$. Assume $N\ge200$, $S>0$,
--   $$\kappa\ \ge\ 64N^2\,\lceil\log\rceil\big(4\cdot100(N+1)^2(S+1)\big)\ =\ \texttt{windowHeavyBound}\ N\ S,$$
--   where $\lceil\log\rceil(x)=\lfloor\log_2x\rfloor+1$, and the window scale is positive: $f.\mathrm{bufferedOptimum}\ \mathrm{old}\ \emptyset\ \kappa>0$. Then window samples with forced reserve $H=\texttt{windowHeavyBound}\ N\ S$ exist, i.e. `Nonempty (WindowSamples W (windowHeavyBound N S))`.
--
--   This is the concentration step for a single window: the fractional entry and exit paths are rounded at finitely many sampled points, with a small forced set absorbing heavy elements, so that all tests (entry/exit endpoints, intersections of consecutive pieces and checkpoints) hold simultaneously with positive probability. The reserve corresponds to the bound with $\theta^{-1}$ of order $N^2\log M$ for $M$ tests, as in Appendix B.2.3.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/WindowSampling.lean#L24-L266 (`ConsistentSubmodular.FractionalWindow.exists_windowSamples`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowSamples

open scoped BigOperators
set_option maxHeartbeats 2000000
open ConsistentSubmodular
open ConsistentSubmodular.FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem ConsistentSubmodular.FractionalWindow.exists_windowSamples (hN : 200 ≤ N) (hS : 0 < S) (hκ : windowHeavyBound N S ≤ κ)
    (hV : 0 < f.bufferedOptimum old ∅ κ) :
    Nonempty (WindowSamples W (windowHeavyBound N S)) := by sorry
