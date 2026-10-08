-- Prove2me | Theorems.Thm_AdamDyn_DecBdd_lyapunov_drift
-- name    : AdamDyn.DecBdd.lyapunov_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:56.157988+00:00
-- url     : https://prove2.me/theorems/6d8ff6c1-3703-489f-a007-380a70224b46
-- title:
--   §9.2, p. 27 — E_n(V_{n+1}) ≤ (1 + C′γ_n²)V_n + Cγ_n² (Robbins–Siegmund form)
-- statement:
--   Assume 2.2, 5.1 (with limits $a,b$) and 5.3 for $F(x)=\mathbb E f(x,\xi)$, with $\varepsilon>0$, $\alpha_1<1$, $\beta_1<1$, and assume $F\ge0$. Then there are constants $C_0,C',C>0$ such that the sequence
--   $$V_n:=(1-C_0\gamma_{n-1}^2)F(x_{n-1})+(1-u_{n-1})P_n$$
--   satisfies, for all $n$ large enough,
--   $$\mathbb E_n(V_{n+1})\le(1+C'\gamma_n^2)\,V_n+C\gamma_n^2 .$$
--
--   Since $\sum_n\gamma_n^2<\infty$, this is the almost-supermartingale inequality to which the Robbins–Siegmund theorem applies; it gives the almost sure convergence of $V_n$, from which coercivity of $F$ bounds $(x_n)$.
--
--   **Formalization Note** $F\ge0$ is the page's "as $\inf F>-\infty$, one can assume without loss of generality that $F\ge0$" (replace $f$ by $f-\inf F$); it is a hypothesis of this milestone only, never of Theorem 5.4. On the page $C_0$ is "the constant $C$ fixed so that (9.4) holds"; here it is existentially quantified. $\mathbb E_n$ is the one-step integral against $\mu$ as in (9.4). Stated at index $n+1$, with $V_{n+1}$ = `lyapV … C₀ n x_n z_{n+1}`; the threshold does not depend on the sample path.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, §9.2, p. 27, display after the definition of V_n

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_Assumptions
import Definitions.Def_AdamDyn_DecBdd_ProofQuantities

open MeasureTheory Filter Topology

namespace AdamDyn.DecBdd

/-- §9.2, p. 27, the Robbins–Siegmund-ready inequality, stated at index `n + 1`: with `F ≥ 0`
(the page's "without loss of generality"), there are constants `C₀, C', C > 0` such that the
sequence `V_{n+1} = (1 - C₀ γ_n²) F(x_n) + (1 - u_n) P_{n+1}` satisfies, for all `n` large enough
and along every run, `E_{n+1}(V_{n+2}) ≤ (1 + C' γ_{n+1}²) V_{n+1} + C γ_{n+1}²`. -/
theorem lyapunov_drift {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ]
    (f : AdamDyn.ConstStep.E d → Ξ → ℝ) (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hε : 0 < ε) (h22 : Assumption22 f gf μ) (h51 : AdamDyn.DecConv.Assumption51 γ α β a b)
    (h53 : Assumption53 f gf μ γ α a b) (hα1 : α 1 < 1) (hβ1 : β 1 < 1)
    (hF0 : ∀ x, 0 ≤ objective f μ x) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ ξs : ℕ → Ξ,
      stepExpect μ gf γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1))
          (lyapV γ α β ε (objective f μ) C₀ (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)).1) ≤
        (1 + C' * γ (n + 1) ^ 2) *
            lyapV γ α β ε (objective f μ) C₀ n (adamRun gf γ α β ε x0 ξs n).1
              (adamRun gf γ α β ε x0 ξs (n + 1))
          + C * γ (n + 1) ^ 2 := by sorry

end AdamDyn.DecBdd
