-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_index_formulations
-- name    : CappeKLUCB.Empirical.index_formulations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:45.889122+00:00
-- url     : https://prove2.me/theorems/8c2d537b-0e35-4f28-965c-851e1fc800de
-- title:
--   §5, p. 15 — sup{E(ν) : ν ∈ ℱ, KL(ν̂, ν) ≤ γ} = sup{E(ν) : ν ∈ 𝔐₁(Supp(ν̂) ∪ {1}), KL(ν̂, ν) ≤ γ}
-- statement:
--   Let $x_1,\dots,x_n\in[0,1]$ with $n\ge1$, let $\hat\nu = \frac1n\sum_{k=1}^n\delta_{x_k}$ be their empirical distribution and let $\gamma>0$. Then
--   $$\sup\bigl\{\mathrm E(\nu) : \nu\in\mathcal F \text{ and } \mathrm{KL}(\hat\nu,\nu)\le\gamma\bigr\} = \sup\bigl\{\mathrm E(\nu) : \nu\in\mathfrak M_1(\mathrm{Supp}(\hat\nu)\cup\{1\}) \text{ and } \mathrm{KL}(\hat\nu,\nu)\le\gamma\bigr\},$$
--   where $\mathcal F$ is the set of finitely supported probability distributions over $[0,1]$ and $\mathfrak M_1(A)$ the set of probability distributions carried by $A$.
--
--   The left side is the index (4) of the generic KL-UCB algorithm in the model $\mathcal F$; the right side is a finite-dimensional convex program, which is how Algorithm 3 computes it. The identity shows that Algorithm 3 is Algorithm 1 for $\mathcal D = \mathcal F$.
--
--   **Formalization Note** The values $x_1,\dots,x_n$ are the first $n$ terms of a real sequence; both suprema are real suprema of nonempty sets bounded above by $1$ ($\hat\nu$ itself belongs to both sets).
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 15, §5, display defining U_a(t) before Algorithm 3

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- The two formulations of the index `U_a(t)`, Cappé et al., arXiv:1210.1136v4, §5, p. 15, display
before Algorithm 3: for the empirical distribution `ν̂` of `n ≥ 1` values in `[0, 1]` and `γ > 0`,
`sup {E(ν) : ν ∈ ℱ, KL(ν̂, ν) ≤ γ} = sup {E(ν) : ν ∈ 𝔐₁(Supp(ν̂) ∪ {1}), KL(ν̂, ν) ≤ γ}`. -/
theorem index_formulations (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hx : ∀ k < n, x k ∈ Set.Icc (0 : ℝ) 1) (γ : ℝ) (hγ : 0 < γ) :
    sSup {m : ℝ | ∃ ν' : Measure ℝ, IsFinSupp01 ν' ∧
        InformationTheory.klDiv (empMeasure x n) ν' ≤ ENNReal.ofReal γ ∧ m = mean ν'}
      = elUpper (empSupp x n) (empMeasure x n) γ := by sorry

end CappeKLUCB.Empirical
