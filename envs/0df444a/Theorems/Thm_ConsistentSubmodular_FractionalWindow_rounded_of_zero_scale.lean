-- Prove2me | Theorems.Thm_ConsistentSubmodular_FractionalWindow_rounded_of_zero_scale
-- name    : ConsistentSubmodular.FractionalWindow.rounded_of_zero_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:40.312197+00:00
-- url     : https://prove2.me/theorems/bfec2fa9-d5e8-4da0-b6b1-dc9be3a2c838
-- title:
--   Rounded window when the window scale is zero
-- statement:
--   Let $W$ be a fractional window (for an objective $f$, ground set `old`, buffers $Q_0\subseteq Q_1\subseteq\cdots$, core budget $\kappa$, accuracy $N$, duration $T$, endpoints `initial`, `terminal`, level $\alpha$ and at most $S$ segments). Assume the window scale vanishes, i.e.
--   $$\mathrm{OPT}_\kappa(\mathrm{old})=f.\mathrm{bufferedOptimum}\ \mathrm{old}\ \emptyset\ \kappa=0 .$$
--   Then for all $H,L\in\mathbb N$ with $L\ge2$ the type of rounded windows `RoundedWindow W H L` is nonempty: there is an entry path and an exit path inside `old` realizing the required endpoints, within the length, cardinality and value requirements of a rounded window.
--
--   This handles the degenerate windows, where all values are zero and no sampling is needed.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/WindowOperationAssembly.lean#L17-L82 (`ConsistentSubmodular.FractionalWindow.rounded_of_zero_scale`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem ConsistentSubmodular.FractionalWindow.rounded_of_zero_scale (hV : f.bufferedOptimum old ∅ κ = 0)
    (H L : ℕ) (hL : 2 ≤ L) : Nonempty (RoundedWindow W H L) := by sorry
