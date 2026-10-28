-- Prove2me | Theorems.Thm_DriverSurge_IC_remark_4
-- name    : DriverSurge.IC.remark_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:30.405913+00:00
-- url     : https://prove2.me/theorems/99fa4874-a978-4668-ae52-7b43a3921f56
-- title:
--   Remark 4, p. 57 — λ_{i→j}T_i − Q_i ≥ 0 and Q_i ≥ 0, both maximized at σ_i = (0, ∞)
-- statement:
--   Let the trip-length laws have finite means. For each state $i$ and every open $\sigma_i\subseteq(0,\infty)$,
--   $$0\le\lambda_{i\to j}T_i(\sigma_i)-Q_i(\sigma_i)\le\lambda_{i\to j}T_i((0,\infty))-Q_i((0,\infty)),\qquad 0\le Q_i(\sigma_i)\le Q_i((0,\infty)).$$
--
--   These bounds make the denominators in $C$ and in the windows of Lemmas 9 and 10 positive.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$.
--
--   Differences from the source:
--   - encoding: $T_i((0,\infty))$ implicitly finite → finite means $\int\tau\,dF_i<\infty$; reason: $T_i((0,\infty))$ is undefined otherwise; only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the inequalities follow from $0\le q_{i\to j}(\tau)\le\lambda_{i\to j}\tau$ for every trip-length law, so they specialize to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Remark 4 (proof p. 65)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 4 (p. 57). With finite mean trip lengths, for every open `s ⊆ (0, ∞)`:
`λ_{i→j}T_i(s) − Q_i(s) ≥ 0`, and it is maximized at `s = (0, ∞)`; `Q_i(s) ≥ 0`, and it is maximized at
`s = (0, ∞)`. -/
theorem remark_4 (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ)
    (hs : IsAdmissible s) :
    0 ≤ P.sw i * Tn P i s - Qn P i s ∧
    P.sw i * Tn P i s - Qn P i s ≤ P.sw i * Tn P i (Ioi 0) - Qn P i (Ioi 0) ∧
    0 ≤ Qn P i s ∧ Qn P i s ≤ Qn P i (Ioi 0) := by sorry

end DriverSurge.IC
