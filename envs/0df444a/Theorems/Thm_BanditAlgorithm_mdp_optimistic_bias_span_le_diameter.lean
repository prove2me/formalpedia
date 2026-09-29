-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_optimistic_bias_span_le_diameter
-- name    : BanditAlgorithm.mdp_optimistic_bias_span_le_diameter
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-03T03:03:04.16941+00:00
-- url     : https://prove2.me/theorems/9cdfb8b9-72cb-4aab-ad5c-401a50c7ea83
-- title:
--   The optimistic bias has span at most the diameter
-- statement:
--   Let $M$ be a finite MDP with reward function $r$ and diameter $D(M)\ge1$, and let $C$ be a family of sets of transition rows containing the true rows of $M$ and admitting an optimistic plan for $r$. Then the bias $v$ of the optimistic plan committed to for $C$ has span at most the diameter:
--   $$v(x)-v(y)\ \le\ D(M)\qquad\text{for all states }x,y.$$
--
--   An optimistic plan satisfies the average-reward Bellman inequality $r(s,a)+\sum_{s'}p(s')v(s')\le\rho+v(s)$ against *every* row $p$ allowed by $C$, in particular against the true row of $M$; so its bias satisfies the Bellman inequality of $M$ itself, with the optimistic gain $\rho\in[0,1]$. The span of the bias of any such inequality is at most $\rho$ times the diameter of $M$, and $\rho\le1$.
--
--   This is the step of the UCRL2 analysis that makes the diameter, rather than the horizon, the scale of the martingale increments and of the estimation error: it is where the optimistic plan is tied back to the true MDP.
--
--   Source: Jaksch, Ortner and Auer, *Near-optimal Regret Bounds for Reinforcement Learning*, JMLR 11 (2010), Section 4.3 (after Lemma 4 and Remark 8); Lattimore and Szepesvari, *Bandit Algorithms* (CUP 2020), Section 38.5.
-- source:
--   Jaksch, Ortner, Auer, JMLR 11 (2010), Sec. 4.3; Lattimore-Szepesvari, Bandit Algorithms, Sec. 38.5

import Definitions.Def_UCRL2Algorithm

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_optimistic_bias_span_le_diameter
    {S A : ℕ} [NeZero A] (hS : 0 < S) (M : FiniteMDP S A)
    (r : Fin S → Fin A → ℝ) (hMr : M.r = r) (hD : 1 ≤ mdpDiameter M)
    (C : Fin S → Fin A → Set (Fin S → ℝ))
    (hmem : ∀ s a, (fun s' ↦ ((M.P s a s' : ℝ))) ∈ C s a)
    (hex : ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      IsOptimisticPlan r C ρ v f q)
    (x y : Fin S) :
    mdpOptimisticBias r C x - mdpOptimisticBias r C y ≤ mdpDiameter M := by
  sorry
