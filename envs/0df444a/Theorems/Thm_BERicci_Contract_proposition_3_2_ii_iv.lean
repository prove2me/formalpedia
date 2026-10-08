-- Prove2me | Theorems.Thm_BERicci_Contract_proposition_3_2_ii_iv
-- name    : BERicci.Contract.proposition_3_2_ii_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:21.451651+00:00
-- url     : https://prove2.me/theorems/e47920dc-6750-43e9-84bb-9848f439d899
-- title:
--   Proposition 3.2 (ii)–(iv), p. 27 — P̃_t is a C_b-preserving version of P_t, dual to H_t, and continuous at t = 0
-- statement:
--   Under the hypotheses of Proposition 3.2 ((MD), a strongly local Dirichlet form with mass-preserving heat flow $(\mathsf P_t)$, and the Lipschitz bound (3.15)), let $(\mathsf H_t)_{t\ge0}$ be the dual semigroup and $\tilde{\mathsf P}_tf(x)=\int_Xf\,d\mathsf H_t\delta_x$. Then for every $t\ge0$:
--
--   1. (ii) $\tilde{\mathsf P}_t$ maps $C_b(X)$ to $C_b(X)$; for every Borel $f\in L^1\cap L^2(X,m)$, $f$ is $\mathsf H_t\delta_x$-integrable for $m$-a.e. $x$ and $\mathsf P_tf(x)=\tilde{\mathsf P}_tf(x)$ for $m$-a.e. $x$;
--   2. (iii) for every bounded Borel $f$, $\tilde{\mathsf P}_tf$ is Borel and
--   $$\int_Xf\,d\mathsf H_t\mu=\int_X\tilde{\mathsf P}_tf\,d\mu\qquad\text{for every }\mu\in\mathscr P(X);\tag{3.20}$$
--
--   and moreover
--   3. (iv) $\lim_{t\downarrow0}\tilde{\mathsf P}_tf(x)=f(x)$ for every $f\in C_b(X)$ and $x\in X$, and for every $\mu\in\mathscr P(X)$ the map $t\mapsto\mathsf H_t\mu$ is weakly continuous on $[0,\infty)$.
--
--   The duality (3.20) is what turns pointwise bounds on $\tilde{\mathsf P}_t$ into bounds on transport costs between the measures $\mathsf H_t\delta_x$.
--
--   **Formalization Note** The identification $\mathsf P_tf=\tilde{\mathsf P}_tf$ is stated for Borel $f\in L^1\cap L^2$, where the heat flow of the Setting is pinned (the paper states it on $L^1$ through the $L^1$ extension of $\mathsf P_t$). The paper's further remarks that $\tilde{\mathsf P}_t$ is defined on nonnegative Borel functions (with values in $[0,\infty]$) and $m$-a.e. on semi-integrable ones are not formalized. Borel measurability of $\tilde{\mathsf P}_tf$ is stated explicitly, since the right side of (3.20) needs it. Weak continuity is tested against bounded continuous functions.
-- source:
--   arXiv:1209.5786v4, Proposition 3.2 (ii)–(iv), (3.20), p. 27

import Mathlib
import Definitions.Def_BERicci_Contract_Bounds

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Proposition 3.2 (ii)–(iv)**, p. 27, for the dual semigroup `H` of (i) and `P̃_t f(x) = ∫ f dH_tδ_x`:
(ii) `P̃_t` maps `C_b(X)` to `C_b(X)`, and `P̃_t f = P_t f` `m`-a.e. for Borel `f ∈ L¹ ∩ L²(X, m)`;
(iii) `∫ f dH_t μ = ∫ P̃_t f dμ` for bounded Borel `f` and `μ ∈ 𝒫(X)`;
(iv) `P̃_t f(x) → f(x)` as `t ↓ 0` for `f ∈ C_b(X)`, and `t ↦ H_t μ` is weakly continuous. -/
theorem proposition_3_2_ii_iv
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (hsupp : m.IsOpenPosMeasure) (hMDb : BERicci.Gamma.MDb m)
    (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P) (hmass : MassPreserving m P)
    (C : ℝ → ℝ≥0) (hC : BoundedOnIntervals C) (h315 : LipContraction m P C)
    (H : ℝ → Measure X → Measure X) (hH : IsDualSemigroup m P H) :
    (∀ t : ℝ, 0 ≤ t →
      (∀ f : BoundedContinuousFunction X ℝ,
        Continuous (Ptilde H t f) ∧ ∃ B : ℝ, ∀ x, |Ptilde H t f x| ≤ B) ∧
      (∀ f : X → ℝ, Measurable f → Integrable f m → MemLp f 2 m →
        (∀ᵐ x ∂m, Integrable f (H t (Measure.dirac x))) ∧ P t f =ᵐ[m] Ptilde H t f) ∧
      (∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
        Measurable (Ptilde H t f) ∧
          ∀ μ : Measure X, IsProbabilityMeasure μ →
            ∫ x, f x ∂(H t μ) = ∫ x, Ptilde H t f x ∂μ)) ∧
    (∀ (f : BoundedContinuousFunction X ℝ) (x : X),
      Tendsto (fun t => Ptilde H t f x) (𝓝[>] 0) (𝓝 (f x))) ∧
    (∀ μ : Measure X, IsProbabilityMeasure μ → ∀ g : BoundedContinuousFunction X ℝ,
      ContinuousOn (fun t => ∫ x, g x ∂(H t μ)) (Set.Ici 0)) := by sorry

end BERicci.Contract
