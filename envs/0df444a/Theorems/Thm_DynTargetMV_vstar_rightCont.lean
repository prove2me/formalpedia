-- Prove2me | Theorems.Thm_DynTargetMV_vstar_rightCont
-- name    : DynTargetMV.vstar_rightCont
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:10.49337+00:00
-- url     : https://prove2.me/theorems/2b233f0e-e781-404e-acbf-bff2ee486010
-- title:
--   p.10 — $v^*$ is right-continuous on $[0,T)$
-- statement:
--   Under Assumptions 1, 2 and 3, the solution $v^*(t)$ of (2.10) is right-continuous in $t\in[0,T)$.
--
--   This gives the measurability of the strategies of Theorem 1, and it places $v^*$ in the uniqueness classes of the theorem.
--
--   Differences from the source:
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
--   - reading: "By Assumptions 1 and 3, we can conclude ... that v* is right-continuous" → Assumption 2 is a hypothesis as well; reason: v* is defined only under Assumption 2, stated just before on the same page, and the stability argument needs its Slater point
--   - encoding: v*(t), the unique solution of (2.10), t ∈ [0,T) → a function v with IsQPSol at every t ∈ [0,T); reason: the solution is unique, so v = v* on [0,T), and v is not used elsewhere
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.10

import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_Assumption2
import Definitions.Def_DynTargetMV_Market_Assumption3
import Definitions.Def_DynTargetMV_Market_IsQPSol

open Set

namespace DynTargetMV

/-- `v*` is right-continuous on `[0,T)`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.10.

**Formalization Note** The source cites Assumptions 1 and 3; Assumption 2 is what makes (2.10) feasible
and supplies the Slater point of the stability argument, so it is a hypothesis too. -/
theorem vstar_rightCont {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    (hA2 : M.Assumption2) {ψ : ℝ → ℝ} (hA3 : M.Assumption3 ψ) {v : ℝ → Fin m → ℝ}
    (hv : ∀ t ∈ Ico 0 M.T, M.IsQPSol ψ t (v t)) :
    ∀ t ∈ Ico 0 M.T, ∀ i, ContinuousWithinAt (fun s => v s i) (Ici t) t := by sorry

end DynTargetMV
