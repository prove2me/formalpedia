-- Prove2me | Theorems.Thm_BERicci_Contract_theorem_3_5
-- name    : BERicci.Contract.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:01.628138+00:00
-- url     : https://prove2.me/theorems/0d94fd91-bfa2-43fe-a5a8-76d534b248be
-- title:
--   Theorem 3.5, p. 30 — (3.15) and (3.16) imply the W₂ contraction W₂(H_tμ, H_tν) ≤ C(t)W₂(μ, ν)
-- statement:
--   Let $(X,\mathsf d)$ be a complete separable metric space which is a length space (3.2), and let $m$ be a Borel measure on $X$ with full support and $m(B_r(x))<\infty$ for all $x\in X$, $r>0$ (condition (MD)). Let $\mathcal E$ be a strongly local Dirichlet form on $L^2(X,m)$ whose heat flow $(\mathsf P_t)_{t\ge0}$ is mass preserving (2.12). Let $C:[0,\infty)\to[0,\infty)$ be bounded on every interval $[0,T]$, and assume
--
--   1. (3.15): $\mathsf P_tf\in\mathrm{Lip}_b(X)$ and $\mathrm{Lip}(\mathsf P_tf)\le C(t)\,\mathrm{Lip}(f)$ for all $t\ge0$, $f\in\mathrm{Lip}_b(X)\cap L^2(X,m)$;
--   2. (3.16): $|D\tilde{\mathsf P}_tf|^2(x)\le C^2(t)\,\tilde{\mathsf P}_t|Df|^2(x)$ for all $t\ge0$, $x\in X$, $f\in\mathrm{Lip}_b(X)\cap L^2(X,m)$,
--
--   where $(\mathsf H_t)$ is the dual semigroup of Proposition 3.2 and $\tilde{\mathsf P}_tg(x)=\int g\,d\mathsf H_t\delta_x$. Then for every $t\ge0$ and all Borel probability measures $\mu,\nu$ on $X$,
--   $$W_2(\mathsf H_t\mu,\mathsf H_t\nu)\le C(t)\,W_2(\mu,\nu).$$
--
--   This is the Kuwada-type duality between pointwise gradient bounds for the heat semigroup and Wasserstein contraction of its dual, in a metric measure setting without doubling or Poincaré assumptions. Combined with Theorem 3.17 of the paper (which gives (3.15) and (3.16) with $C(t)=e^{-Kt}$ under $\mathrm{BE}(K,\infty)$), it yields Corollary 3.18: $W_2((\mathsf P_tf)m,(\mathsf P_tg)m)\le e^{-Kt}W_2(fm,gm)$ for probability densities $f,g$.
--
--   **Formalization Note** The paper states an equivalence; its proof establishes only this direction, citing Kuwada [34] for the converse, which is not posed (it would also require the dual semigroup to exist without (3.15)). The inequality is stated for squares, $W_2^2(\mathsf H_t\mu,\mathsf H_t\nu)\le C(t)^2W_2^2(\mu,\nu)$ in $[0,\infty]$, over all of $\mathscr P(X)$ as printed. The dual semigroup is a binder `H` with the predicate `IsDualSemigroup`, which determines it on probability measures; the heat flow is likewise a pinned binder. The σ-algebra is Borel rather than its $m$-completion, and mass preservation is stated on $L^1\cap L^2$.
-- source:
--   arXiv:1209.5786v4, Theorem 3.5 (direction (3.15)+(3.16) ⇒ (W2-cont)), p. 30; proof pp. 30–31

import Mathlib
import Definitions.Def_BERicci_Contract_Bounds

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Theorem 3.5**, p. 30 (the direction proved in the paper): under (2.1), (2.12), (MD) and the
length property (3.2), the bounds (3.15) and (3.16) imply (W₂-cont):
`W₂(H_t μ, H_t ν) ≤ C(t) W₂(μ, ν)` for all `μ, ν ∈ 𝒫(X)`, `t ≥ 0` (written for squares, in `[0, ∞]`). -/
theorem theorem_3_5
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (hsupp : m.IsOpenPosMeasure) (hMDb : BERicci.Gamma.MDb m)
    (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P) (hmass : MassPreserving m P)
    (hlen : BERicci.Gamma.IsLengthSpace X)
    (C : ℝ → ℝ≥0) (hC : BoundedOnIntervals C) (h315 : LipContraction m P C)
    (H : ℝ → Measure X → Measure X) (hH : IsDualSemigroup m P H) (h316 : GradBound m H C) :
    ∀ t : ℝ, 0 ≤ t → ∀ μ ν : Measure X, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      BERicci.Gamma.W2sq (H t μ) (H t ν) ≤ ((C t : ℝ≥0∞)) ^ 2 * BERicci.Gamma.W2sq μ ν := by sorry

end BERicci.Contract
