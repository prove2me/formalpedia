-- Prove2me | Theorems.Thm_ConsistentSubmodular_FractionalWindow_retained_tests_extend
-- name    : ConsistentSubmodular.FractionalWindow.retained_tests_extend
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:49.681406+00:00
-- url     : https://prove2.me/theorems/3f3b8713-8215-4236-af90-d6079fd8946a
-- title:
--   Tests at the retained times extend to all times of the window
-- statement:
--   Let $W$ be a fractional window for an objective $f$, an old set $\mathrm{old}\subseteq[n]$, a monotone buffer sequence $Q_0\subseteq Q_1\subseteq\cdots$, core budget $\kappa$, grid parameter $N$, duration $T$ and level $\alpha$; let $t_0\le\dots\le t_{3N+1}$ be its retained times $W.\mathrm{retained}$. Write $\mathrm{OPT}(\mathrm{old},Q)=\max\{f(Q\cup C):C\subseteq\mathrm{old},|C|\le\kappa\}$ for the buffered optimum. Let $N>0$, let $A\subseteq[n]$ and $\mathrm{loss}\ge0$. Assume that at every retained time
--
--   $$\alpha\,\mathrm{OPT}(\mathrm{old},Q_{t_i})-\mathrm{loss}\;\le\;f(Q_{t_i}\cup A)\qquad\text{for all } i\in\{0,\dots,3N+1\}.$$
--
--   Then for every $t\le T$,
--
--   $$\alpha\,\mathrm{OPT}(\mathrm{old},Q_t)-\mathrm{loss}-\alpha\cdot\frac{\mathrm{OPT}(\mathrm{old},\emptyset)}{N}\;\le\;f(Q_t\cup A).$$
--
--   The tests at the retained times thus extend to all arrival times of the window at the additional loss $\alpha\,\mathrm{OPT}(\mathrm{old},\emptyset)/N$. This is used to reduce the verification of a rounded set against all times to the finitely many retained ones.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/WindowTransfer.lean#L19-L47 (`ConsistentSubmodular.FractionalWindow.retained_tests_extend`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem ConsistentSubmodular.FractionalWindow.retained_tests_extend (hN : 0 < N) (A : Finset (Fin n)) (loss : ℝ) (hloss : 0 ≤ loss)
    (htests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ - loss ≤
      f.value (Q (W.retained i) ∪ A)) :
    ∀ t, t ≤ T → α * f.bufferedOptimum old (Q t) κ - loss-
      α * (f.bufferedOptimum old ∅ κ / N) ≤ f.value (Q t ∪ A) := by sorry
