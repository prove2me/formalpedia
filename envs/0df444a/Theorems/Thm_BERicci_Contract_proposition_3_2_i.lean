-- Prove2me | Theorems.Thm_BERicci_Contract_proposition_3_2_i
-- name    : BERicci.Contract.proposition_3_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:46.561635+00:00
-- url     : https://prove2.me/theorems/8a9088ad-e97c-4d56-9254-78b70529c415
-- title:
--   Proposition 3.2 (i), p. 27 — under (3.15) the dual semigroup H_t exists, is unique, and contracts W_(β) and W₁
-- statement:
--   Let $(X,\mathsf d)$ be a complete separable metric space with a Borel measure $m$ of full support and finite on balls (condition (MD)). Let $\mathcal E$ be a strongly local Dirichlet form on $L^2(X,m)$ whose heat flow $(\mathsf P_t)_{t\ge0}$ is mass preserving (2.12), and assume the Lipschitz bound (3.15) with a function $C$ bounded on every interval $[0,T]$.
--
--   Then there is a family $(\mathsf H_t)_{t\ge0}$ with $\mathsf H_t(fm)=(\mathsf P_tf)m$ for every probability density $f\in L^1\cap L^2(X,m)$, mapping $\mathscr P(X)$ to $\mathscr P(X)$ continuously for the weak convergence; on $\mathscr P(X)$ it is unique with these properties; and for every $t\ge0$, $\mu,\nu\in\mathscr P(X)$ and every continuous, concave, bounded modulus $\beta$ with $0=\beta(0)<\beta(r)$ for $r>0$,
--   $$W_{(\beta)}(\mathsf H_t\mu,\mathsf H_t\nu)\le(C(t)\vee1)\,W_{(\beta)}(\mu,\nu),\qquad W_1(\mathsf H_t\mu,\mathsf H_t\nu)\le C(t)\,W_1(\mu,\nu).$$
--
--   This is the construction of the dual semigroup on which the rest of the section rests: the pointwise version $\tilde{\mathsf P}_t$, the gradient bound (3.16) and the $W_2$ contraction are all stated through $\mathsf H_t$.
--
--   **Formalization Note** The paper's "uniquely extends to a $W_{(\beta)}$-Lipschitz map" is rendered as existence of a family satisfying the dual-semigroup predicate (weak continuity, which is $W_{(\beta)}$-continuity since $W_{(\beta)}$ metrizes weak convergence, p. 25) together with uniqueness on probability measures among all such families. Distances are in $[0,\infty]$. The heat flow is given as a binder pinned by its defining property; mass preservation is stated on $L^1\cap L^2$.
-- source:
--   arXiv:1209.5786v4, Proposition 3.2 (i), (3.18), (3.19), p. 27

import Mathlib
import Definitions.Def_BERicci_Contract_Bounds

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Proposition 3.2 (i)**, p. 27: under (2.1), (2.12), (MD) and (3.15), the map `H_t(f m) := (P_t f) m`
extends uniquely to a weakly (equivalently `W_(β)`-) continuous map `H_t : 𝒫(X) → 𝒫(X)`, which satisfies
(3.18) `W_(β)(H_t μ, H_t ν) ≤ (C(t) ∨ 1) W_(β)(μ, ν)` for every admissible modulus `β` and
(3.19) `W₁(H_t μ, H_t ν) ≤ C(t) W₁(μ, ν)`. -/
theorem proposition_3_2_i
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (hsupp : m.IsOpenPosMeasure) (hMDb : BERicci.Gamma.MDb m)
    (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P) (hmass : MassPreserving m P)
    (C : ℝ → ℝ≥0) (hC : BoundedOnIntervals C) (h315 : LipContraction m P C) :
    ∃ H : ℝ → Measure X → Measure X, IsDualSemigroup m P H ∧
      (∀ H' : ℝ → Measure X → Measure X, IsDualSemigroup m P H' →
        ∀ t : ℝ, 0 ≤ t → ∀ μ : Measure X, IsProbabilityMeasure μ → H' t μ = H t μ) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ μ ν : Measure X, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        (∀ β : ℝ → ℝ, IsModulus β →
          Wbeta β (H t μ) (H t ν) ≤ ENNReal.ofReal (max (C t : ℝ) 1) * Wbeta β μ ν) ∧
        W1 (H t μ) (H t ν) ≤ (C t : ℝ≥0∞) * W1 μ ν := by sorry

end BERicci.Contract
