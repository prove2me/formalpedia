-- Prove2me | Theorems.Thm_BauerleRiederMDP_Stopping_theorem_10_2_3
-- name    : BauerleRiederMDP.Stopping.theorem_10_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:21.205204+00:00
-- url     : https://prove2.me/theorems/80b30db2-ac57-4d38-98d4-efaff27f711a
-- title:
--   Theorem 10.2.3 — the stopping region $S^*$ (corrected: optimality of $\tau^*$ needs the limit form of (B))
-- statement:
--   Consider a stationary stopping problem with unbounded horizon under Assumption (B), with $d_n$, $S_n^*$ as in Theorem 10.1.5, $J=\lim_nJ_n$, and $G_f=\liminf_n J_{nf}$.
--
--   1. The limit $d:=\lim_{n\to\infty}d_n$ exists. With $S^*:=\{x\mid d(x)\ge0\}$ we have $S^*=\bigcap_nS_n^*=\{x\mid J(x)=g(x)\}$, and $f^*:=1_{S^*}$ is a maximizer of $J$.
--   2. If $G_{f^*}\ge TG_{f^*}$ and $\mathbb P_x(\tau_{f^*}<\infty)=1$ for all $x\in E$, then $G_{f^*}=V_\infty^*$. If in addition the limit form of (B) in Remark 10.2.1 a) holds, then $\tau^*:=\inf\{n\in\mathbb N_0\mid X_n\in S^*\}$ is an optimal stopping time and
--
--   $$
--   G_{f^*}(x)=\mathbb E_x[R_{\tau^*}]=V_\infty^*(x),\qquad x\in E.
--   $$
--
--   The theorem identifies the stopping region of the unbounded problem and says when entering it is optimal.
--
--   Differences from the source:
--   - correction: b) τ* := inf{n | X_n ∈ S*} is optimal and G_{f*} = E_x[R_τ*] under (B) as printed → assumes in addition the limit form of (B) printed in Remark 10.2.1 a), lim_n E_x[R_{τ∧n}] = E_x[R_τ] for all τ < ∞; reason: the printed claim is false. Chain on E = ℕ₀ ∪ {s}: from k to k+1 or s with probability 1/2 each, s absorbing, c = 0, β = 1, g(k) = 2^k − 1/2, g(s) = 0. It satisfies (B): g ≥ 0 gives the liminf part by Fatou and sup_τ E_k[g(X_τ)] ≤ 2^k. Yet τ*, the hitting time of s, is a.s. finite with E_x[R_τ*] = 0 while V*(0) ≥ g(0) = 1/2. Remark 10.2.1 a) calls the limit form equivalent to (B), which this chain refutes
--   - encoding: J_n := sup over stopping times τ ≤ n, J := lim_n J_n → the iterate P.J n and P.Jlim = sup_n P.J n; reason: Theorem 10.1.5 a) (a milestone here) identifies the iterate with the supremum under (B_n), and (B) gives every (B_n); same values
--   - encoding: τ < ∞ with P_x(τ < ∞) = 1 for all x → τ with P_x(τ = ⊤) = 0 for the x at hand, inside the platform definitions of (B) and V*; reason: a stopping time finite under P_x is P_x-a.s. equal to one finite under every P_y (set it to 0 on the X_0-event where P_y(τ < ∞) ≠ 1), so the conditions and values agree
--   - encoding: integrals in [−∞, ∞) and policies as decision rules f : E → {0,1} → erealIntegral = ∫v⁺ − ∫v⁻ in EReal; a stationary rule is its stopping set S; reason: Lean convention; same instances. Under (B) the positive part is finite, so ∞ − ∞ never arises in these expressions
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.2.3, p.312

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim

open MeasureTheory Filter Topology
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- **Theorem 10.2.3** (corrected), Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), p.312 (PDF 320), under (B).
a) `d := lim_n d_n` exists; `S^* := {d ≥ 0} = ∩_n S_n^* = {J = g}` and `f^* := 1_{S^*}` is a
maximizer of `J`.
b) If `G_{f^*} ≥ T G_{f^*}` and `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `G_{f^*} = V_∞^*`; under the
limit form of (B) (Remark 10.2.1 a)) also `τ^* := inf{n | X_n ∈ S^*}` is optimal and
`G_{f^*}(x) = 𝔼_x[R_{τ^*}] = V_∞^*(x)`.

**Formalization Note.** The optimality of `τ^*` is false under (B) as printed: a counterexample is
in the Differences section of the natural-language statement. -/
theorem theorem_10_2_3 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr) :
    (∃ d : E → EReal,
      (∀ x : E, Tendsto (fun n => P.d n x) atTop (𝓝 (d x))) ∧
      ({x : E | 0 ≤ d x} = ⋂ n : ℕ, P.stopSet n) ∧
      ({x : E | 0 ≤ d x} = {x : E | P.Jlim x = (P.g x : EReal)}) ∧
      P.IsMaximizer {x : E | 0 ≤ d x} P.Jlim) ∧
    ((∀ x : E, P.T (P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)}) x ≤
        P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x) →
      (∀ x : E, Pr x {w | P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)} w = ⊤} = 0) →
      (∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x = P.Vstar Pr x) ∧
      (AssumptionBLim P Pr →
        P.IsOptimal Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) ∧
        ∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x =
          P.EReward Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) x)) := by sorry

end BauerleRiederMDP.Stopping
