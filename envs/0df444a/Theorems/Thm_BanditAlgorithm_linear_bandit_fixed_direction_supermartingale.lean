-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_fixed_direction_supermartingale
-- name    : BanditAlgorithm.linear_bandit_fixed_direction_supermartingale
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T14:46:42.854184+00:00
-- url     : https://prove2.me/theorems/9822508c-fac0-41aa-ab41-8b765f6f80c3
-- title:
--   Lemma 20.2: fixed-direction exponential supermartingale
-- statement:
--   On a standard Borel probability space with a discrete-time filtration $(\mathcal F_t)$, let $A_{t+1}\in\mathbb R^d$ be $\mathcal F_t$-measurable and let $\eta_{t+1}$ be $\mathcal F_{t+1}$-measurable and conditionally $1$-subgaussian given $\mathcal F_t$. Define
--
--   $$
--   S_t=\sum_{s=1}^{t}\eta_sA_s,
--   \qquad
--   V_t(\lambda)=\lambda I+\sum_{s=1}^{t}A_sA_s^\top.
--   $$
--
--   For every $\lambda\ge0$ and every fixed $x\in\mathbb R^d$, the process
--
--   $$
--   M_t(x)=\exp\!\left(\langle x,S_t\rangle-\frac12x^\top V_t(\lambda)x\right)
--   $$
--
--   is a nonnegative supermartingale, and $M_0(x)\le1$.
--
--   This fixed-direction exponential supermartingale is the basic concentration object used by the method of mixtures. Integrating it over directions produces the mixture process underlying the self-normalized martingale bound.
--
--   **Formalization Note** Conditional subgaussianity is represented by Mathlib's `HasCondSubgaussianMGF`; the theorem permits predictable, random, and unbounded actions.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), printed pp. 257-258, Lemma 20.2 and its proof.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_SelfNormalizedProcess

open MeasureTheory ProbabilityTheory Matrix

theorem BanditAlgorithm.linear_bandit_fixed_direction_supermartingale
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 ≤ lam) (x : Fin d → ℝ) :
    Supermartingale (selfNormalizedProcess d lam η A x) ℱ P ∧
      ∀ ω : Ω, selfNormalizedProcess d lam η A x 0 ω ≤ 1 := by
  sorry
