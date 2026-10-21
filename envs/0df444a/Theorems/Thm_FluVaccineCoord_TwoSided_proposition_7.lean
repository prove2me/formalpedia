-- Prove2me | Theorems.Thm_FluVaccineCoord_TwoSided_proposition_7
-- name    : FluVaccineCoord.TwoSided.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:46.622618+00:00
-- url     : https://prove2.me/theorems/49b94282-4576-430f-8b15-ef5d7f4bde74
-- title:
--   Proposition 7, p. 22 — the modified incentive program coordinates, is ex-ante budget-neutral and splits welfare as V_H − K and K + W⁽ᶜ⁾ − V_H
-- statement:
--   Fix $x^c_1$ satisfying (8), a socially-optimal planned quantity $Q^{(c)} \ge 0$ (a maximizer of $W^{(c)}$ of (9) over $Q \ge 0$), and a constant $K$. The planner offers the modified incentive program $I = (t, r(Q_r), T(Q_r))$: the incentive $r$ of (18), the transfer $T$ of (19), and a lump-sum tax $t = K - K_{bn}$ on every individual, with $K_{bn}$ of (24). Then:
--
--   1. the program is ex-ante budget-neutral:
--   $$t = \mathbb E_Y\bigl[S^{(I)}(YQ^{(c)})\bigr];$$
--   2. the manufacturer voluntarily produces a socially-optimal quantity: $Q^{(c)}$ maximizes its expected profit $\pi^{(I)}$ of (17), and every maximizer of $\pi^{(I)}$ maximizes $W^{(c)}$;
--   3. (i) the individuals' total expected utility, with thresholds $x^{(I)}$ and tax $t$, equals $V_H - K$, and the manufacturer's expected profit $\pi^{(I)}(Q^{(c)})$ equals $K + W^{(c)}(Q^{(c)}) - V_H$;
--   4. for every equilibrium production quantity $Q^{(d)} \ge 0$ without a program (a maximizer of $\pi^{(d)}$ of (15)): (ii) if $K > \underline K$ (23), then $\pi^{(d)}(Q^{(d)}) < \pi^{(I)}(Q^{(c)})$; (iii) if $K < \bar K$ (22), the individuals' total expected utility without a program is smaller than under the modified program.
--
--   Choosing $K$ divides the maximal expected social welfare $W^{(c)}$ between individuals and manufacturer at will, while the planner's budget balances in expectation.
--
--   **Formalization Note** "Under the modified program" means at its equilibrium. Individuals use the threshold rule with the incentive $r$, computed from the primitives; the manufacturer's choice is concluded (item 2), not assumed. The coordination claim of the paragraph before the proposition (p. 22) is item 2. The individuals' total utility integrates the utilities of p. 13 over $x \sim U[0,\bar x]$, with vaccination cost $w + p - r$ and the tax $t$. The comparisons hold for every maximizer $Q^{(d)}$ of $\pi^{(d)}$; its existence is not assumed.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), p. 22, §6.3 and Proposition 7, with (18), (19), (21)–(24)

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- Proposition 7, p. 22, with the coordination claim of the paragraph before it. Let `Q⁽ᶜ⁾` be
socially optimal and let the planner offer the modified program `(t, r(Qᵣ), T(Qᵣ))` of (18)–(19)
with `t = K − K_bn` (24). Then the program is ex-ante budget-neutral, `t = E_Y[S⁽ᴵ⁾(YQ⁽ᶜ⁾)]`; the
manufacturer voluntarily produces a socially-optimal quantity (`Q⁽ᶜ⁾` maximizes `π⁽ᴵ⁾`, and every
maximizer of `π⁽ᴵ⁾` maximizes `W⁽ᶜ⁾`); (i) the individuals' total expected utility is `V_H − K` and
the manufacturer's expected profit is `K + W⁽ᶜ⁾ − V_H`; and, against any equilibrium production
`Q⁽ᵈ⁾` of the chain without a program, (ii) `K > K̲` makes the manufacturer better off and
(iii) `K < K̄` makes the individuals better off. -/
theorem proposition_7 (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1)
    (Qc : ℝ) (hQc0 : 0 ≤ Qc) (hQc : IsMaxOn (Wc M xc1) (Ici 0) Qc) (K : ℝ) :
    K - Kbn M xc1 Qc = ∫ y, Snet M xc1 K (y * Qc) ∂M.μ ∧
      IsMaxOn (piI M xc1 K) (Ici 0) Qc ∧
      (∀ Q, 0 ≤ Q → IsMaxOn (piI M xc1 K) (Ici 0) Q → IsMaxOn (Wc M xc1) (Ici 0) Q) ∧
      EUtilI M xc1 (K - Kbn M xc1 Qc) Qc = M.VH - K ∧
      piI M xc1 K Qc = K + Wc M xc1 Qc - M.VH ∧
      (∀ Qd, 0 ≤ Qd → IsMaxOn (piD M) (Ici 0) Qd →
        Kunder M xc1 Qc Qd < K → piD M Qd < piI M xc1 K Qc) ∧
      (∀ Qd, 0 ≤ Qd → IsMaxOn (piD M) (Ici 0) Qd →
        K < Kover M Qd → EUtilD M Qd < EUtilI M xc1 (K - Kbn M xc1 Qc) Qc) := by sorry

end FluVaccineCoord.TwoSided
