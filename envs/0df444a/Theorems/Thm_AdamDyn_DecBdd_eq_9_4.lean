-- Prove2me | Theorems.Thm_AdamDyn_DecBdd_eq_9_4
-- name    : AdamDyn.DecBdd.eq_9_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:51.090963+00:00
-- url     : https://prove2.me/theorems/b15d7b51-0b53-44d0-a963-9b54847409e7
-- title:
--   (9.4) — conditional drift of F(x_n) + P_{n+1}
-- statement:
--   Assume 2.2, 5.1 (with limits $a,b$) and 5.3 for $F(x)=\mathbb E f(x,\xi)$, with $\varepsilon>0$, $\alpha_1<1$, $\beta_1<1$. Write $\mathbb E_n$ for the conditional expectation given $\mathcal F_n=\sigma(\xi_1,\dots,\xi_n)$. For every $\delta>0$ there is $C>0$ such that for all $n$ large enough,
--   $$\mathbb E_n\big(F(x_n)+P_{n+1}\big)\le F(x_{n-1})+P_n+u_n\,\mathbb E_n(P_{n+1})-2\Big(a-\frac{b+\delta}4\Big)\gamma_nP_n+C\gamma_n^2\big(1+F(x_n)+P_n\big),$$
--   with $u_n=1-a_{n+1}/a_n$ and $P_n$ as in §9.2.
--
--   This is the drift inequality for the potential $F(x_{n-1})+P_n$ that the Robbins–Siegmund theorem is applied to; the negative term $-2(a-(b+\delta)/4)\gamma_nP_n$ is where the condition $b<4a$ enters.
--
--   **Formalization Note** The page writes $u_nP_{n+1}$ on the right-hand side; $P_{n+1}$ is not $\mathcal F_n$-measurable, and the derivation (taking $\mathbb E_n$ of (9.2), $u_n$ deterministic) gives $u_n\mathbb E_n(P_{n+1})$, which is what is stated. $\mathbb E_n G(z_{n+1})$ is written as the one-step integral $\int G(T_{n+1}(z_n,\xi))\,\mu(d\xi)$, a version of the conditional expectation under Assumption 4.1; the inequality is stated for every realization of the past, so Assumption 4.1 is not a hypothesis here. The page's "without loss of generality $F\ge0$" is not needed for (9.4) and not assumed. Stated at index $n+1$: the threshold "$n$ large enough" depends only on $\delta$ and the sequences, not on the sample path, and $C$ depends on $\delta$. Integrability of $\xi\mapsto P_{n+2}(T_{n+2}(z_{n+1},\xi))$ follows from Assumption 5.3 ii) and the measurability in Assumption 2.2.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, §9.2, p. 27, Eq. (9.4)

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_Assumptions
import Definitions.Def_AdamDyn_DecBdd_ProofQuantities

open MeasureTheory Filter Topology

namespace AdamDyn.DecBdd

/-- (9.4), §9.2, p. 27, stated at index `n + 1`, with `E_{n+1}` the one-step conditional
expectation `stepExpect` and the page's `u_{n+1} P_{n+2}` read as `u_{n+1} E_{n+1}(P_{n+2})`:
for every `δ > 0` there is `C > 0` such that for all `n` large enough, along every run,
`F(x_{n+1}) + E_{n+1}P_{n+2} ≤ F(x_n) + P_{n+1} + u_{n+1} E_{n+1}P_{n+2}
  - 2(a - (b+δ)/4) γ_{n+1} P_{n+1} + C γ_{n+1}² (1 + F(x_{n+1}) + P_{n+1})`. -/
theorem eq_9_4 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : AdamDyn.ConstStep.E d → Ξ → ℝ) (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hε : 0 < ε) (h22 : Assumption22 f gf μ) (h51 : AdamDyn.DecConv.Assumption51 γ α β a b)
    (h53 : Assumption53 f gf μ γ α a b) (hα1 : α 1 < 1) (hβ1 : β 1 < 1) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ ξs : ℕ → Ξ,
      objective f μ (adamRun gf γ α β ε x0 ξs (n + 1)).1
          + stepExpect μ gf γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1))
              (potP γ α β ε (n + 2)) ≤
        objective f μ (adamRun gf γ α β ε x0 ξs n).1
          + potP γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1))
          + uSeq γ α (n + 1) * stepExpect μ gf γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1))
              (potP γ α β ε (n + 2))
          - 2 * (a - (b + δ) / 4) * γ (n + 1) * potP γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1))
          + C * γ (n + 1) ^ 2 * (1 + objective f μ (adamRun gf γ α β ε x0 ξs (n + 1)).1
              + potP γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1))) := by sorry

end AdamDyn.DecBdd
