-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_9_3_4
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_9_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:05:23.594386+00:00
-- url     : https://prove2.me/theorems/9d82c291-b55c-562d-b9a7-0864dd72c9a1
-- title:
--   Theorem 9.3.4 — pure jump market: value iteration, fixed point, error bound, optimal strategy, policy iteration, Howard
-- statement:
--   a) The value function $V(t, x)$ of the terminal wealth problem satisfies $V = J_\infty  = J \in  IM_cv$, where $J := \lim _{n\to \infty } T^n U$. b) $V(t, x)$ is the unique fixed point of $T$ in $IM_cv$. c) For $g \in  IM_cv$: $\|V - T^n g\|_b \le  \alpha _b^n/(1 - \alpha _b) \|T g - g\|_b$. d) There exists an optimal Markov portfolio strategy $\pi ^* = (\pi ^*_t)$ with $\pi ^*_t = f^*(T_n, Z_n)(t - T_n)$, $t \in  (T_n, T_{n+1}]$, for a decision rule $f^* : E \to  A$. e) The policy iteration holds. f) Howard's policy improvement algorithm holds.
--
--   **Formalization Note.** $\gamma  \ge  0$ is large enough that $\alpha _\gamma  < 1$ (with $\gamma  + \lambda  - \bar{\mu} > 0$), the standing choice of p.285; `b = bfun γ` and $\alpha _b$ is `JumpMarket.alphaB` ($\alpha _b \le  \alpha _\gamma $, Proposition 9.3.2). $U$ is a utility function on $[0, \infty )$ with values in $\mathbb R _+$, identified with $(t, x) \mapsto  U(x)$. $T$ is the operator (9.15) (`Treal`, on real functions); all statements are on $E$. e) is Theorem 7.3.6 c), d) for the model with relaxed controls $R$ (Young topology): with the $n$-stage values $J_n = T^n 0$ of that model and $D^*_n$, $D^*_\infty $ the maximum points of $\alpha  \mapsto  L J_n(t, x, \alpha )$ and of $\alpha  \mapsto  L V(t, x, \alpha )$, $\emptyset  \ne  Ls D^*_n(t, x) \subset  D^*_\infty (t, x)$, and a relaxed rule with values in $Ls D^*_n$ gives an optimal stationary relaxed policy. f) is Theorem 7.5.1 a), c) for decision rules $f : E \to  A$: an improvement of $f$ is better (strictly on $E_0$), and a rule that cannot be improved is optimal.
--
--   Differences from the source:
--   - reading: γ large enough (p.285) → γ ≥ 0 with γ + λ − μ̄ > 0 and α_γ < 1; reason: the book's standing choice of γ
--   - reading: "the policy iteration holds", "Howard's algorithm holds" → Theorem 7.3.6 c), d) on relaxed controls; Theorem 7.5.1 a), c) on decision rules; reason: the results the proof cites
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 9.3.4, p.287-288 (PDF 297)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_relaxedStage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Jinf
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Vstrat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_markovJMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset
import Definitions.Def_MDPFinance_Contracting_LsSet
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_normb
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_IMcv
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_muBar
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaGamma
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaB
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Treal

open Filter Topology
open BauerleRiederMDP.PDMDP
open BauerleRiederMDP.RegimeSwitching (IsUtilityFunction)
open MDPFinance.Contracting (LsSeq)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 9.3.4** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 9.3.4, pp.287–288, PDF 297–298, model of §9.3, pp.280–285, PDF 290–295).
a) The value function `V(t, x)` of the terminal wealth problem satisfies `V = J_∞ = J ∈ IM_cv`,
where `J := lim_{n→∞} T^n U`.
b) `V(t, x)` is the unique fixed point of `T` in `IM_cv`.
c) For `g ∈ IM_cv`: `‖V − T^n g‖_b ≤ α_b^n/(1 − α_b) ‖T g − g‖_b`.
d) There exists an optimal Markov portfolio strategy `π* = (π*_t)` with
`π*_t = f*(T_n, Z_n)(t − T_n)`, `t ∈ (T_n, T_{n+1}]`, for a decision rule `f* : E → A`.
e) The policy iteration holds.
f) Howard's policy improvement algorithm holds.

**Formalization Note.** `γ ≥ 0` is large enough that `α_γ < 1` (with `γ + λ − μ̄ > 0`), the standing
choice of p.285; `b = bfun γ` and `α_b` is `JumpMarket.alphaB` (`α_b ≤ α_γ`, Proposition 9.3.2).
`U` is a utility function on `[0, ∞)` with values in `ℝ_+`, identified with `(t, x) ↦ U(x)`. `T` is
the operator (9.15) (`Treal`, on real functions); all statements are on `E`. e) is Theorem 7.3.6
c), d) for the model with relaxed controls `R` (Young topology): with the `n`-stage values
`J_n = T^n 0` of that model and `D*_n`, `D*_∞` the maximum points of `α ↦ L J_n(t, x, α)` and of
`α ↦ L V(t, x, α)`, `∅ ≠ Ls D*_n(t, x) ⊂ D*_∞(t, x)`, and a relaxed rule with values in `Ls D*_n`
gives an optimal stationary relaxed policy. f) is Theorem 7.5.1 a), c) for decision rules
`f : E → A`: an improvement of `f` is better (strictly on `E_0`), and a rule that cannot be improved
is optimal. -/
theorem theorem_9_3_4 {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ)
    (hU : IsUtilityFunction U (Set.Ici 0)) (hU0 : ∀ x, 0 ≤ x → 0 ≤ U x)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγμ : 0 < γ + Mk.lam - Mk.muBar) (hαγ : Mk.alphaGamma γ < 1) :
    let Uf : ℝ × ℝ → ℝ := fun p => U p.2
    let αb := Mk.alphaB γ
    let Jn : ℕ → ℝ × ℝ → EReal := fun n => (Mk.relaxedStage U).T^[n] 0
    let Dn : ℕ → ℝ × ℝ → Set (RelaxedControl (Ufrac d)) := fun n p =>
      {α | ∀ α', (Mk.relaxedStage U).L (Jn n) p α' ≤ (Mk.relaxedStage U).L (Jn n) p α}
    let Dinf : ℝ × ℝ → Set (RelaxedControl (Ufrac d)) := fun p =>
      {α | ∀ α', (Mk.relaxedStage U).L (Mk.V U) p α' ≤ (Mk.relaxedStage U).L (Mk.V U) p α}
    -- a) and b)
    (∃ J : ℝ × ℝ → ℝ, J ∈ Mk.IMcv γ U ∧
      (∀ p ∈ Mk.Eset, Tendsto (fun n => (Mk.Treal U)^[n] Uf p) atTop (𝓝 (J p)) ∧
        Mk.V U p = (J p : EReal) ∧ Mk.Jinf U p = (J p : EReal)) ∧
      (∀ p ∈ Mk.Eset, Mk.Treal U J p = J p) ∧
      (∀ w ∈ Mk.IMcv γ U, (∀ p ∈ Mk.Eset, Mk.Treal U w p = w p) → ∀ p ∈ Mk.Eset, w p = J p) ∧
      -- c)
      ∀ g ∈ Mk.IMcv γ U, ∀ n : ℕ,
        Mk.normb γ (fun p => J p - (Mk.Treal U)^[n] g p) ≤
          αb ^ n / (1 - αb) * Mk.normb γ (fun p => Mk.Treal U g p - g p)) ∧
    -- d)
    (∃ fstar : DecisionRule (ℝ × ℝ) (Ufrac d),
      ∀ p ∈ Mk.Eset, Mk.Vstrat U (markovJMStrategy fun _ => fstar) p = Mk.V U p) ∧
    -- e) policy iteration on relaxed controls
    ((∀ p ∈ Mk.Eset, (LsSeq fun n => Dn n p).Nonempty ∧ LsSeq (fun n => Dn n p) ⊆ Dinf p) ∧
      ∃ frel : RelaxedDecisionRule (ℝ × ℝ) (Ufrac d),
        (∀ p ∈ Mk.Eset, frel.control p ∈ LsSeq fun n => Dn n p) ∧
        ∀ p ∈ Mk.Eset, (Mk.relaxedStage U).Jinf (fun _ => frel.control) p = Mk.V U p) ∧
    -- f) Howard's policy improvement
    (∀ f : DecisionRule (ℝ × ℝ) (Ufrac d),
      let Jf : ℝ × ℝ → EReal := (Mk.stage U).Jinf fun _ => f.control
      let Dxf : ℝ × ℝ → Set (ControlFn (Ufrac d)) := fun p => {α | Jf p < (Mk.stage U).L Jf p α}
      (∀ (E0 : Set (ℝ × ℝ)), MeasurableSet E0 → ∀ h : DecisionRule (ℝ × ℝ) (Ufrac d),
        (∀ p ∈ E0 ∩ Mk.Eset, h.control p ∈ Dxf p) → (∀ p, p ∉ E0 → h.control p = f.control p) →
        (∀ p ∈ Mk.Eset, Jf p ≤ (Mk.stage U).Jinf (fun _ => h.control) p) ∧
          ∀ p ∈ E0 ∩ Mk.Eset, Jf p < (Mk.stage U).Jinf (fun _ => h.control) p) ∧
      ((∀ p ∈ Mk.Eset, Dxf p = ∅) → ∀ p ∈ Mk.Eset, Jf p = Mk.Jinf U p)) := by sorry

end BauerleRiederMDP.LQ.Supplement
