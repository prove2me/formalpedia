-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_residual_process_bounds
-- name    : BellWilliams2001.ThresholdPolicy.residual_process_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:31:27.080984+00:00
-- url     : https://prove2.me/theorems/a614bdd4-7d40-41b0-95c3-7e9b8ca348ff
-- title:
--   Theorem 7.2 — the residual process stays within $\pm(L^r-1)$ of the threshold
-- statement:
--   There is a constant $c_0>0$, depending only on the model data, with the following property. Let $c>c_0$ and let $T^{r,*}$ follow the threshold policy with $L^r=[c\log r]$. Let $\tau_0^r=\inf\{t\ge0:Q_1^r(t)\ge L^r\}$ (with $\inf\emptyset=\infty$) and let $R^r(t)=Q_1^r(t)-L^r$ be the residual process (50). Then for each $t\ge0$ and $\varepsilon>0$, as $r\to\infty$,
--   $$\mathbf P\big(I_1^r(\tau_0^r)\ge r\varepsilon\big)\to0,\qquad \mathbf P\Big(\sup_{\tau_0^r\le s\le r^2t}|R^r(s)|\ge L^r-1\Big)\to0,$$
--   with the conventions that $I_1^r(\tau_0^r)=\lim_{t\to\infty}I_1^r(t)$ on $\{\tau_0^r=\infty\}$ and that a supremum over an empty set is $-\infty$.
--
--   The first limit says server 1 idles only for a negligible time before the class 1 queue first reaches the threshold; the second says that afterwards the queue stays within $L^r-1$ of the threshold on the diffusion time scale.
--
--   **Formalization Note** $I_1^r(\tau_0^r)$ is written as $\sup\{I_1^r(s): 0\le s\le\tau_0^r\}$ in $[0,\infty]$, which equals the page's quantity in both cases because $I_1^r$ is continuous and nondecreasing. Because $R^r$ is integer valued and takes finitely many values on compact intervals, the second event is $\{\exists s\in[\tau_0^r,r^2t]: |R^r(s)|\ge L^r-1\}$, which is empty when $\tau_0^r>r^2t$. The threshold relations are required only for the systems with $L^r\ge1$ (all but finitely many).
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 624, Theorem 7.2, (50)–(52); p. 621, Definition 5.1

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

open MeasureTheory Filter Topology
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-- Theorem 7.2 (p. 624). There is `c₀ > 0` (depending only on the model data) such that for
every `c > c₀` and every sequence of threshold policies `T^{r,*}` with threshold `L^r = [c log r]`
(required for the systems with `L^r ≥ 1`), with `τ^r_0 = inf{t ≥ 0 : Q^r_1(t) ≥ L^r}` (in
`[0,∞]`, `inf ∅ = ∞`) and the residual process `R^r = Q^r_1 − L^r` (50), for each `t ≥ 0` and
`ε > 0`:
(51) `P(I^r_1(τ^r_0) ≥ rε) → 0`, where `I^r_1(τ^r_0)` is `sup{I^r_1(s) : s ≤ τ^r_0}`, which is
`I^r_1(τ^r_0)` when `τ^r_0 < ∞` and `lim_{t→∞} I^r_1(t)` on `{τ^r_0 = ∞}` (the page's
convention), `I^r_1` being nondecreasing and continuous;
(52) `P(sup_{τ^r_0 ≤ s ≤ r²t} |R^r(s)| ≥ L^r − 1) → 0`, the supremum over an empty interval being
`−∞`; since `R^r` is integer valued with finitely many values on compacts, the event is
`{∃ s ∈ [τ^r_0, r²t], |R^r(s)| ≥ L^r − 1}`. -/
theorem residual_process_bounds {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε →
        let τ₀ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
          ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : (M.threshold c n : ℝ) ≤ M.queue n (Tstar n) ω 0 s),
            ENNReal.ofReal s
        Tendsto (fun n => M.P {ω | ENNReal.ofReal (M.r n * ε) ≤
            ⨆ (s : ℝ) (_ : 0 ≤ s) (_ : ENNReal.ofReal s ≤ τ₀ n ω),
              ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 s)}) atTop (𝓝 0) ∧
        Tendsto (fun n => M.P {ω | ∃ s : ℝ, 0 ≤ s ∧ τ₀ n ω ≤ ENNReal.ofReal s ∧
            s ≤ M.r n ^ 2 * t ∧
            (M.threshold c n : ℝ) - 1 ≤ |M.queue n (Tstar n) ω 0 s - (M.threshold c n : ℝ)|})
          atTop (𝓝 0) := by sorry

end BellWilliams2001.ThresholdPolicy
