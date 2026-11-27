-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_7_5_1
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_7_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:59:03.494779+00:00
-- url     : https://prove2.me/theorems/eeb335e1-f262-42ad-a6a8-6b3b6bf95883
-- title:
--   Theorem 7.5.1 — Howard's policy improvement: improvement and the two optimality criteria
-- statement:
--   Let (C) be satisfied. For a decision rule $f \in  F$ denote $D(x, f) := \{a \in  D(x) | L J_f(x, a) > J_f(x)\}$, $x \in  E$. Then: a) if for some measurable $E_0 \subset  E$ a decision rule $h$ satisfies $h(x) \in  D(x, f)$ for $x \in  E_0$ and $h(x) = f(x)$ for $x \notin  E_0$, then $J_h \ge  J_f$ and $J_h(x) > J_f(x)$ for $x \in  E_0$; b) if $D(x, f) = \emptyset $ for all $x \in  E$, $J_f \ge  0$ and $T : IB \to  IB$, then $J_f = J_\infty $, i.e. the stationary policy $(f, f, \dots )$ is optimal; c) let $b$ be a bounding function, $\beta  \alpha _b < 1$ and $T : IB_b \to  IB_b$; if $D(x, f) = \emptyset $ for all $x \in  E$, then $J_f = J_\infty $.
--
--   **Formalization Note.** The model, $L$, $T$, $IB$, $IB_b$, $J_\infty $ and the policy values `J_f = Jinfpi M r (f, f, …)` are the published `MDPFinance.Contracting` objects; the Integrability Assumption (A) ($\delta  < \infty $) and the Convergence Assumption (C) of §7.1, standing assumptions of the chapter, are hypotheses. $E$ and $A$ are arbitrary measurable spaces (the proof uses only reward iteration, monotonicity of $T_h$, (C) and Banach's fixed point theorem). In c) $T : IB_b \to  IB_b$ is read with the extended-real operator $T$: for every $v \in  IB_b$, $T v$ is (the cast of) a function of $IB_b$. The strict inequality in a) holds at every point of $E_0$.
--
--   Differences from the source:
--   - generalization: E, A Borel spaces (§7.2) → arbitrary measurable spaces; reason: the proof uses only reward iteration, monotonicity of T_h, (C) and Banach's fixed point theorem; Borel spaces are a special case
--   - encoding: T : IB_b → IB_b → for v ∈ IB_b, the extended-real T v is the cast of a function of IB_b; reason: reads the hypothesis with the EReal operator; same condition
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 7.5.1, p.212 (PDF 223)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_BauerleRiederMDP_Contracting_ConvergenceAssumptionC

open MeasureTheory ProbabilityTheory Filter
open MDPFinance.Contracting
open BauerleRiederMDP.Contracting (ConvergenceAssumptionC)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 7.5.1 (Howard's policy improvement)** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Theorem 7.5.1, p.212, PDF 223). Let (C) be satisfied. For a
decision rule `f ∈ F` denote `D(x, f) := {a ∈ D(x) | L J_f(x, a) > J_f(x)}`, `x ∈ E`. Then:
a) if for some measurable `E_0 ⊂ E` a decision rule `h` satisfies `h(x) ∈ D(x, f)` for `x ∈ E_0`
and `h(x) = f(x)` for `x ∉ E_0`, then `J_h ≥ J_f` and `J_h(x) > J_f(x)` for `x ∈ E_0`;
b) if `D(x, f) = ∅` for all `x ∈ E`, `J_f ≥ 0` and `T : IB → IB`, then `J_f = J_∞`, i.e. the
stationary policy `(f, f, …)` is optimal;
c) let `b` be a bounding function, `β α_b < 1` and `T : IB_b → IB_b`; if `D(x, f) = ∅` for all
`x ∈ E`, then `J_f = J_∞`.

**Formalization Note.** The model, `L`, `T`, `IB`, `IB_b`, `J_∞` and the policy values
`J_f = Jinfpi M r (f, f, …)` are the published `MDPFinance.Contracting` objects; the Integrability
Assumption (A) (`δ < ∞`) and the Convergence Assumption (C) of §7.1, standing assumptions of the
chapter, are hypotheses. `E` and `A` are arbitrary measurable spaces (the proof uses only reward
iteration, monotonicity of `T_h`, (C) and Banach's fixed point theorem). In c) `T : IB_b → IB_b` is
read with the extended-real operator `T`: for every `v ∈ IB_b`, `T v` is (the cast of) a function
of `IB_b`. The strict inequality in a) holds at every point of `E_0`. -/
theorem theorem_7_5_1 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (hA : IntegrabilityAssumptionA M)
    (hC : ConvergenceAssumptionC M) (f : E → A) (hf : IsDecisionRuleOf M f) :
    let Jf : E → EReal := Jinfpi M M.r (fun _ => f)
    let Dxf : E → Set A := fun x => {a | a ∈ M.Dx x ∧ Jf x < L M Jf (x, a)}
    -- a) improvement
    (∀ E0 : Set E, MeasurableSet E0 → ∀ h : E → A, IsDecisionRuleOf M h →
        (∀ x ∈ E0, h x ∈ Dxf x) → (∀ x, x ∉ E0 → h x = f x) →
        (∀ x, Jf x ≤ Jinfpi M M.r (fun _ => h) x) ∧
          ∀ x ∈ E0, Jf x < Jinfpi M M.r (fun _ => h) x) ∧
    -- b) no improvement, J_f ≥ 0 and T : IB → IB
    ((∀ x, Dxf x = ∅) → (∀ x, 0 ≤ Jf x) → (∀ v ∈ IB M, T M v ∈ IB M) → Jf = Jinf M) ∧
    -- c) no improvement in a contracting model with T : IB_b → IB_b
    (∀ (b : E → ℝ) (cr αb : ℝ), IsBoundingFunction M b cr αb → M.β * αb < 1 →
        (∀ v ∈ IBb b, ∃ w ∈ IBb b, T M (fun y => (v y : EReal)) = fun y => (w y : EReal)) →
        (∀ x, Dxf x = ∅) → Jf = Jinf M) := by sorry

end BauerleRiederMDP.LQ.Supplement
