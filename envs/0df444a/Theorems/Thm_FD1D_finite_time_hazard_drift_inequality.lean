-- Prove2me | Theorems.Thm_FD1D_finite_time_hazard_drift_inequality
-- name    : FD1D.finite_time_hazard_drift_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:46.783076+00:00
-- url     : https://prove2.me/theorems/583b9367-c677-4b52-8225-49c19d3fde09
-- title:
--   FD1 D: finite time hazard drift inequality
-- statement:
--   The finite-`T` inequality used in Section 5.  Here `Phi`, `D`, `R`, and `H`
--   are already expectations at time `t`; the preceding theorem supplies their
--   telescoped drift equation.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L292-L346
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L292-L346

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.finite_time_hazard_drift_inequality
    {T : ℕ} {a L c B : ℝ} (Phi D R H : ℕ → ℝ)
    (hT : 0 < T)
    (hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t)
    (hD : ∀ t < T, a * (H t / 100 - c) ≤ D t)
    (hR : ∀ t < T, R t ≤ L * H t)
    (hPhi0 : 0 ≤ Phi 0) (hPhiT : Phi T ≤ B) :
    (a / 100 - L) *
        ((∑ t ∈ Finset.range T, H t) / T) ≤
      a * c + B / T := by sorry
