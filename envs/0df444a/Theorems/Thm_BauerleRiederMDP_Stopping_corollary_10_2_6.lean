-- Prove2me | Theorems.Thm_BauerleRiederMDP_Stopping_corollary_10_2_6
-- name    : BauerleRiederMDP.Stopping.corollary_10_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:23.982008+00:00
-- url     : https://prove2.me/theorems/27e573e5-6afa-4386-8192-c994d623c6dc
-- title:
--   Corollary 10.2.6 — sufficient conditions for $G_{f^*}=J$ and for optimality of $\tau_{f^*}$ (corrected: b), c) need the limit form of (B))
-- statement:
--   Consider a stationary stopping problem with unbounded horizon under Assumption (B), and let $f^*$ be a maximizer of $J$.
--
--   1. If the corresponding Markov Decision Problem has a bounding function $b$ with $\beta\alpha_b<1$, then $G_{f^*}=J$. Moreover, if $\mathbb P_x(\tau_{f^*}<\infty)=1$ for all $x\in E$, then $\tau_{f^*}$ is an optimal stopping time.
--   2. If $\sup_{x\in E}c(x)<0$, $\beta=1$ and $G_{f^*}=J$, then $\mathbb P_x(\tau_{f^*}<\infty)=1$ for all $x\in E$. If in addition the limit form of (B) in Remark 10.2.1 a) holds, then $\tau_{f^*}$ is an optimal stopping time.
--   3. If $J-g$ is bounded from above and $\mathbb P_x(\tau_{f^*}<\infty)=1$ for all $x\in E$, then $G_{f^*}=J$. If in addition the limit form of (B) holds, then $\tau_{f^*}$ is an optimal stopping time.
--
--   These are checkable conditions under which a maximizer of $J$ yields an optimal stopping rule, which Example 10.2.5 of the book shows is not automatic.
--
--   Differences from the source:
--   - correction: b) and c) τ_{f*} is an optimal stopping time under (B) as printed → assumes in addition the limit form of (B) printed in Remark 10.2.1 a), lim_n E_x[R_{τ∧n}] = E_x[R_τ] for all τ < ∞; reason: the printed claim is false. Chain on E = ℕ₀ ∪ {s}: from k to k+1 or s with probability 1/2 each, s absorbing, c = 0, β = 1, g(k) = 2^k − 1/2, g(s) = 0. It satisfies (B): g ≥ 0 gives the liminf part by Fatou and sup_τ E_k[g(X_τ)] ≤ 2^k. Yet τ*, the hitting time of s, is a.s. finite with E_x[R_τ*] = 0 while V*(0) ≥ g(0) = 1/2. Remark 10.2.1 a) calls the limit form equivalent to (B), which this chain refutes. For b) take c ≡ −1/4 and g(k) = 2^k − 3/4 on the same chain: G_{f*} = J (J(k) = 2^k − 1/2, J(s) = 0), but E_0[R_τ*] = −1/2 < 1/2 = V*(0). For c) the first chain has J − g ≤ 1/2
--   - encoding: J_n := sup over stopping times τ ≤ n, J := lim_n J_n → the iterate P.J n and P.Jlim = sup_n P.J n; reason: Theorem 10.1.5 a) (a milestone here) identifies the iterate with the supremum under (B_n), and (B) gives every (B_n); same values
--   - encoding: τ < ∞ with P_x(τ < ∞) = 1 for all x → τ with P_x(τ = ⊤) = 0 for the x at hand, inside the platform definitions of (B) and V*; reason: a stopping time finite under P_x is P_x-a.s. equal to one finite under every P_y (set it to 0 on the X_0-event where P_y(τ < ∞) ≠ 1), so the conditions and values agree
--   - encoding: integrals in [−∞, ∞) and policies as decision rules f : E → {0,1} → erealIntegral = ∫v⁺ − ∫v⁻ in EReal; a stationary rule is its stopping set S; reason: Lean convention; same instances. Under (B) the positive part is finite, so ∞ − ∞ never arises in these expressions
--   - encoding: sup_x c(x) < 0 → ∃ s < 0 with c ≤ s; reason: the same condition on nonempty E; on empty E the clause is vacuous
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Corollary 10.2.6, p.314

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim

open MeasureTheory Filter Topology
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- **Corollary 10.2.6** (corrected), Bäuerle & Rieder, Markov Decision Processes with Applications
to Finance (2011), p.314 (PDF 322), under (B), for a maximizer `f^* = 1_S` of `J`.
a) If the Markov Decision Model has a bounding function `b` with `βα_b < 1`, then `G_{f^*} = J`; if
moreover `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `τ_{f^*}` is optimal.
b) If `sup c < 0`, `β = 1` and `G_{f^*} = J`, then `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`; under the limit
form of (B) (Remark 10.2.1 a)) also `τ_{f^*}` is optimal.
c) If `J − g` is bounded above and `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `G_{f^*} = J`; under the
limit form of (B) also `τ_{f^*}` is optimal.

**Formalization Note.** The optimality claims of b) and c) are false under (B) as printed: see the
Differences section of the natural-language statement. Part a) is as printed. `sup c < 0` is
`∃ s < 0, c ≤ s`. `BoundingFunction` carries one constant `cr` for `c` and `g`; the maximum of the
page's `c_r, c_g` serves. -/
theorem corollary_10_2_6 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S : Set E) (hS : P.IsMaximizer S P.Jlim) :
    (∀ B : P.BoundingFunction, P.beta * B.alpha < 1 →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      ((∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ s : ℝ, s < 0 ∧ ∀ x : E, P.c x ≤ s) → P.beta = 1 → (∀ x : E, P.Gf Pr S x = P.Jlim x) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) ∧
      (AssumptionBLim P Pr → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ C : ℝ, ∀ x : E, P.Jlim x ≤ (P.g x : EReal) + (C : EReal)) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      (AssumptionBLim P Pr → P.IsOptimal Pr (P.ruleTime S))) := by sorry

end BauerleRiederMDP.Stopping
