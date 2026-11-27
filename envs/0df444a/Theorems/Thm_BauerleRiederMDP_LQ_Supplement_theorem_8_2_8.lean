-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_8_2_8
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_8_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:01:19.475739+00:00
-- url     : https://prove2.me/theorems/d6f3e597-1a68-4455-91b3-2a848cefc247
-- title:
--   Theorem 8.2.8 — HJB verification theorem for piecewise deterministic Markov decision processes
-- statement:
--   Let a Piecewise Deterministic Markov Decision Process be given with a bounding function $b$, $\alpha _b < 1$ and $\mathbb E ^\pi _x[e^{-\beta t} b(X_t)] \to  0$ for $t \to  \infty $ for all $\pi $, $x$. Suppose that $v \in  C¹(E) \cap  IB_b$ is a solution of the HJB equation $\sup _{u \in  U} {A v(x, u) + r(x, u)} = \beta  v(x)$, $x \in  E$, with the generator $A v(x, u) = \mu (x, u) v_x + \lambda  \int  (v(y) - v(x)) Q(dy|x, u)$, and that $f^*$ is a maximizer of the HJB equation and defines a state process $(X^*_t)$. Then $v = V_\infty $ and $\pi ^*_t := f^*(X^*_{t-})$ is an optimal Markov policy (in feedback form).
--
--   **Formalization Note.** The model is the published `PDMDP.Model` ($E$ a Borel subset of $\mathbb R ^d$). $\alpha _b$ is the published `alphaB` of the embedded model with relaxed controls (as in the published Theorem 8.2.6), the discrete-time modulus. $v \in  C¹(E)$: $v$ is the restriction to $E$ of a function $v : \mathbb R ^d \to  \mathbb R $ that is continuously differentiable on an open set $O \supseteq  E$, and $v_x$ is its derivative; $v|_E \in  IB_b$ (measurable, $|v| \le  c b$). Transversality is required for all Markov policies and all $x$. "$f^*$ defines a state process" (8.9): for every post-jump state $z$ there is a solution $\psi (z, \cdot )$ in $E$ of $dx_t = \mu (x_t, f^*(x_t)) dt$, $x_0 = z$, jointly measurable through $f^*$; the policy $\pi ^*$ applies after each jump $T_n$ the control function $s \mapsto  f^*(\psi (Z_n, s))$, so $\pi ^*_t = f^*(X^*_{t-})$. Optimality is $V_{\pi ^*} = V_\infty $ on $E$, $V_\infty $ the published supremum (8.3) over Markov policies.
--
--   Differences from the source:
--   - reading: v ∈ C^1(E) → v is continuously differentiable on an open set O ⊇ E, v_x its derivative; reason: E is only a Borel subset of ℝ^d; this is the standard meaning of C^1(E)
--   - reading: f* defines a state process (X*_t) → a measurable family ψ(z,·) of solutions in E of dx_t = μ(x_t, f*(x_t))dt, x_0 = z; reason: the feedback equation (8.9) between jumps
--   - encoding: α_b < 1 → the published relaxed-control modulus alphaB < 1 (as in Theorem 8.2.6); reason: the book's α_b of p.251
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.8, p.255 (PDF 266)

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_Model
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_Vinf
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_PDIsBounding

open MeasureTheory ProbabilityTheory Filter Topology
open BauerleRiederMDP.PDMDP
open MDPFinance.Contracting (IBb)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 8.2.8 (Verification Theorem)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 8.2.8, p.255, PDF 266, HJB equation (8.8) and feedback
control (8.9), p.255). Let a Piecewise Deterministic Markov Decision Process be given with a
bounding function `b`, `α_b < 1` and `𝔼^π_x[e^{−βt} b(X_t)] → 0` for `t → ∞` for all `π`, `x`.
Suppose that `v ∈ C¹(E) ∩ IB_b` is a solution of the HJB equation
`sup_{u ∈ U} {A v(x, u) + r(x, u)} = β v(x)`, `x ∈ E`, with the generator
`A v(x, u) = μ(x, u) v_x + λ ∫ (v(y) − v(x)) Q(dy|x, u)`, and that `f*` is a maximizer of the HJB
equation and defines a state process `(X*_t)`. Then `v = V_∞` and `π*_t := f*(X*_{t−})` is an
optimal Markov policy (in feedback form).

**Formalization Note.** The model is the published `PDMDP.Model` (`E` a Borel subset of `ℝ^d`).
`α_b` is the published `alphaB` of the embedded model with relaxed controls (as in the published
Theorem 8.2.6), the discrete-time modulus. `v ∈ C¹(E)`: `v` is the restriction to `E` of a
function `v : ℝ^d → ℝ` that is continuously differentiable on an open set `O ⊇ E`, and `v_x` is its
derivative; `v|_E ∈ IB_b` (measurable, `|v| ≤ c b`). Transversality is required for all Markov
policies and all `x`. "`f*` defines a state process" (8.9): for every post-jump state `z` there is a
solution `ψ(z, ·)` in `E` of `dx_t = μ(x_t, f*(x_t)) dt`, `x_0 = z`, jointly measurable through
`f*`; the policy `π*` applies after each jump `T_n` the control function
`s ↦ f*(ψ(Z_n, s))`, so `π*_t = f*(X*_{t−})`. Optimality is `V_{π*} = V_∞` on `E`, `V_∞` the
published supremum (8.3) over Markov policies. -/
theorem theorem_8_2_8 {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {U : Type*}
    [MeasurableSpace U] (M : Model E U) (b : E → ℝ) (hb : PDIsBounding M.toJumpModel b)
    (hα : M.relaxedStage.alphaB b < 1)
    (htrans : ∀ (π : ℕ → DecisionRule E U) (x : E),
      Tendsto (fun t : ℝ => ∫⁻ ω, ENNReal.ofReal (Real.exp (-M.β * t) * b (M.X π ω t)) ∂(M.law π x))
        atTop (𝓝 0))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) (O : Set (EuclideanSpace ℝ (Fin d))) (hO : IsOpen O)
    (hEO : E ⊆ O) (hv : ContDiffOn ℝ 1 v O) (hvb : (fun x : E => v x) ∈ IBb b)
    (hHJB : ∀ x : E, (⨆ u : U, ((fderiv ℝ v x (M.μ (x, u)) +
        M.lam * ∫ y, (v y - v x) ∂(M.Q (x, u)) + M.r (x, u) : ℝ) : EReal)) =
      ((M.β * v x : ℝ) : EReal))
    (fstar : E → U) (hfstar_meas : Measurable fstar)
    (hfstar : ∀ (x : E) (u : U),
      fderiv ℝ v x (M.μ (x, u)) + M.lam * ∫ y, (v y - v x) ∂(M.Q (x, u)) + M.r (x, u) ≤
        fderiv ℝ v x (M.μ (x, fstar x)) + M.lam * ∫ y, (v y - v x) ∂(M.Q (x, fstar x)) +
          M.r (x, fstar x))
    (ψ : E → ℝ → E) (hψ : Measurable fun p : ℝ × E => fstar (ψ p.2 p.1))
    (hψsol : ∀ z : E,
      IsRelaxedSolution M.μ
        (DecisionRule.control (⟨fun p : ℝ × E => fstar (ψ p.2 p.1), hψ⟩ : DecisionRule E U)
          z).toRelaxed z (ψ z)) :
    (∀ x : E, ((v x : ℝ) : EReal) = M.Vinf x) ∧
      ∀ x : E, M.Vpi (fun _ => (⟨fun p : ℝ × E => fstar (ψ p.2 p.1), hψ⟩ : DecisionRule E U)) x =
        M.Vinf x := by sorry

end BauerleRiederMDP.LQ.Supplement
