-- Prove2me | Theorems.Thm_AdamDyn_DecBdd_eq_9_1
-- name    : AdamDyn.DecBdd.eq_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:46.61419+00:00
-- url     : https://prove2.me/theorems/e0239a14-270a-40ec-8413-43de2a7dbf91
-- title:
--   (9.1) — descent inequality F(x_n) ≤ F(x_{n−1}) − γ_n⟨∇F(x_n), m̂_n/(ε+√v̂_n)⟩ + Cγ_n²P_n
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be differentiable with a Lipschitz continuous gradient (Assumption 5.3 i)). Let the stepsizes satisfy Assumption 5.1 with limits $a,b$, let $\varepsilon>0$, $\alpha_1<1$, $\beta_1<1$, and let $(x_n,m_n,v_n)$ be the iterates of Algorithm 5.1 along any sample path, with any gradient values. Then there is a constant $C>0$ such that for every $n\ge1$ with $a_n=(1-\alpha_{n+1})/\gamma_n>0$,
--   $$F(x_n)\le F(x_{n-1})-\gamma_n\Big\langle\nabla F(x_n),\frac{\hat m_n}{\varepsilon+\sqrt{\hat v_n}}\Big\rangle+C\gamma_n^2P_n,$$
--   where $P_n=\frac1{2a_nr_n}\langle m_n^{\odot2},1/(\varepsilon+\sqrt{\hat v_n})\rangle$.
--
--   This is the first step of the proof of Theorem 5.4: the decrease of the objective along an Adam step, up to a second-order term controlled by the potential $P_n$.
--
--   **Formalization Note** Stated at index $n+1$ for $n\in\mathbb N$ (so $n+1\ge1$), with the guard $\alpha_{n+2}<1$, i.e. $a_{n+1}>0$; under Assumption 5.1 iv) this holds for all large $n$, and without it $P$ would be $0$ by Lean's division convention. $C$ is chosen before the sample path and the index: it depends only on the Lipschitz constant, $\varepsilon$ and the sequences. The inequality is deterministic (it holds for every realization), and $F$ is any differentiable function with Lipschitz gradient — in Theorem 5.4 it is $F(x)=\mathbb E f(x,\xi)$, which is $C^1$ under Assumption 2.2.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, §9.2, p. 26, Eq. (9.1)

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_Assumptions
import Definitions.Def_AdamDyn_DecBdd_ProofQuantities

open Filter Topology

namespace AdamDyn.DecBdd

/-- (9.1), §9.2, p. 26: the descent inequality
`F(x_n) ≤ F(x_{n-1}) - γ_n ⟨∇F(x_n), m̂_n/(ε + √v̂_n)⟩ + C γ_n² P_n`, for a differentiable `F`
with Lipschitz gradient, along every run of Algorithm 5.1, at every index `n ≥ 1` with `a_n > 0`
(stated at index `n + 1`). -/
theorem eq_9_1 {d : ℕ} {Ξ : Type*} (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (F : AdamDyn.ConstStep.E d → ℝ)
    (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hε : 0 < ε) (h51 : AdamDyn.DecConv.Assumption51 γ α β a b) (hα1 : α 1 < 1) (hβ1 : β 1 < 1)
    (hF : Differentiable ℝ F) (hL : ∃ L : NNReal, LipschitzWith L (gradient F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξs : ℕ → Ξ) (n : ℕ), α (n + 2) < 1 →
      F (adamRun gf γ α β ε x0 ξs (n + 1)).1 ≤
        F (adamRun gf γ α β ε x0 ξs n).1
          - γ (n + 1) * inner ℝ (gradient F (adamRun gf γ α β ε x0 ξs (n + 1)).1)
              (adamDir α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)))
          + C * γ (n + 1) ^ 2 * potP γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) := by sorry

end AdamDyn.DecBdd
