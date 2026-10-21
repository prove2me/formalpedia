-- Prove2me | Theorems.Thm_FluVaccineCoord_TwoSided_proposition_6
-- name    : FluVaccineCoord.TwoSided.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:39.948329+00:00
-- url     : https://prove2.me/theorems/9028b79a-25a3-4d9b-9d2c-54bf1c59e261
-- title:
--   Proposition 6, p. 21 — participation (K > K̲, K_bn < K̄) and ex-ante budget neutrality (K = K_bn) of the program (18)–(19)
-- statement:
--   Fix $x^c_1$ satisfying (8), a socially-optimal planned quantity $Q^{(c)} \ge 0$ (a maximizer of $W^{(c)}$ over $Q \ge 0$), and a constant $K$, and let the planner offer the program $(r, T)$ of (18)–(19). Let $Q^{(d)} \ge 0$ be any equilibrium production quantity without a program (a maximizer of $\pi^{(d)}$ of (15)).
--
--   1. If $K > \underline K = V_H + \pi^{(d)}(Q^{(d)}) - W^{(c)}(Q^{(c)})$ (23), the manufacturer's expected profit under the program exceeds its profit without it: $\pi^{(d)}(Q^{(d)}) < \pi^{(I)}(Q^{(c)})$.
--   2. If $K_{bn} < \bar K = V_H + \pi^{(d)}(Q^{(d)}) - W^{(d)}(Q^{(d)})$ ((24), (22)), the individuals' total expected utility under the program exceeds their total expected utility without it, whatever $K$.
--   3. If $K = K_{bn}$, the program is ex-ante budget-neutral:
--   $$\mathbb E_Y\bigl[S^{(I)}(YQ^{(c)})\bigr] = 0.$$
--
--   Under the program the manufacturer produces $Q^{(c)}$ (Proposition 5), so its expected profit is $\pi^{(I)}(Q^{(c)})$.
--
--   **Formalization Note** Under the program the individuals use the equilibrium threshold $x^{(I)}$ and receive $r$ per vaccination, with no lump-sum tax; without it they use $x^{(d)}$. The comparison holds for every maximizer $Q^{(d)}$ of $\pi^{(d)}$; its existence is not assumed.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), p. 21, Proposition 6, with (21)–(24)

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- Proposition 6, p. 21: let `Q⁽ᶜ⁾` be socially optimal and `Q⁽ᵈ⁾` any equilibrium production of
the chain without a program (a maximizer of `π⁽ᵈ⁾` of (15)). (i) If `K > K̲` (23), the
manufacturer's expected profit under the program, `π⁽ᴵ⁾ = π⁽ᴵ⁾(Q⁽ᶜ⁾)`, exceeds `π⁽ᵈ⁾`; (ii) if
`K_bn < K̄` ((24), (22)), the individuals' total expected utility under the program exceeds that
without it, whatever `K`; (iii) if `K = K_bn`, the program is ex-ante budget-neutral,
`E_Y[S⁽ᴵ⁾(YQ⁽ᶜ⁾)] = 0` (21). -/
theorem proposition_6 (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1)
    (Qc : ℝ) (hQc0 : 0 ≤ Qc) (hQc : IsMaxOn (Wc M xc1) (Ici 0) Qc) (K : ℝ) :
    (∀ Qd, 0 ≤ Qd → IsMaxOn (piD M) (Ici 0) Qd →
        Kunder M xc1 Qc Qd < K → piD M Qd < piI M xc1 K Qc) ∧
      (∀ Qd, 0 ≤ Qd → IsMaxOn (piD M) (Ici 0) Qd →
        Kbn M xc1 Qc < Kover M Qd → EUtilD M Qd < EUtilI M xc1 0 Qc) ∧
      (K = Kbn M xc1 Qc → ∫ y, Snet M xc1 K (y * Qc) ∂M.μ = 0) := by sorry

end FluVaccineCoord.TwoSided
