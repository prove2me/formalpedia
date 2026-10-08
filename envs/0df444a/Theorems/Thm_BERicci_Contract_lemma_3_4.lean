-- Prove2me | Theorems.Thm_BERicci_Contract_lemma_3_4
-- name    : BERicci.Contract.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:50.325477+00:00
-- url     : https://prove2.me/theorems/7d184fae-e17c-449b-bc62-f07113aa2ffb
-- title:
--   Lemma 3.4, p. 29 — P̃_tQ₁f(x) − P̃_tf(y) ≤ ½C²(t)d²(x,y) under (3.15), (3.16) and the length property
-- statement:
--   Let $(X,\mathsf d)$ be a complete separable length space ((3.2)) with a Borel measure $m$ of full support and finite on balls. Let $\mathcal E$ be a strongly local Dirichlet form on $L^2(X,m)$ whose heat flow $(\mathsf P_t)$ is mass preserving, let $(\mathsf H_t)$ be its dual semigroup and $\tilde{\mathsf P}_t$ the pointwise version, and assume (3.15) and (3.16) with a function $C$ bounded on every $[0,T]$. Let $Q_s$ be the Hopf–Lax map (3.5).
--
--   For every $f\in\mathrm{Lip}_b(X)$, nonnegative and with bounded support:
--   1. for every $s\ge0$, $Q_sf$ is Lipschitz, nonnegative and has bounded support;
--   2. for every $t\ge0$ and $x,y\in X$,
--   $$\tilde{\mathsf P}_tQ_1f(x)-\tilde{\mathsf P}_tf(y)\le\tfrac12C^2(t)\,\mathsf d^2(x,y).$$
--
--   Through Kantorovich duality this one-sided bound yields the transport estimate (3.26) between the measures $\mathsf H_t\delta_x$ and $\mathsf H_t\delta_y$.
--
--   **Formalization Note** The paper prints $|\tilde{\mathsf P}_tQ_1f(x)-\tilde{\mathsf P}_tf(y)|\le\frac12C^2(t)\mathsf d^2(x,y)$. With the absolute value the claim fails at $x=y$ (it would force $\tilde{\mathsf P}_t(f-Q_1f)(x)=0$, false at $t=0$ for a steep bump $f$, where $Q_1f\ne f$). The proof bounds $g(1)-g(0)=\tilde{\mathsf P}_tQ_1f(x)-\tilde{\mathsf P}_tf(y)$ from above, and only this one-sided bound is used in (3.26); that is what is stated. The paper's "$Q_tf$ is Lipschitz, …" is read for every time parameter $s\ge0$, as the proof uses it for $s\in[0,1]$. The semigroup $\mathsf P_t$ in the inequality is the pointwise version $\tilde{\mathsf P}_t$, as everywhere in §3.2.
-- source:
--   arXiv:1209.5786v4, Lemma 3.4, p. 29 (proof pp. 29–30)

import Mathlib
import Definitions.Def_BERicci_Contract_Bounds

namespace BERicci.Contract

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Lemma 3.4**, p. 29, with the one-sided inequality the proof establishes (the printed absolute
value fails at `x = y`): for `f ∈ Lip_b(X)` nonnegative with bounded support, every `Q_s f`, `s ≥ 0`, is
Lipschitz, nonnegative with bounded support, and `P̃_t Q₁ f(x) − P̃_t f(y) ≤ ½ C²(t) d²(x, y)`. -/
theorem lemma_3_4
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (hsupp : m.IsOpenPosMeasure) (hMDb : BERicci.Gamma.MDb m)
    (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P) (hmass : MassPreserving m P)
    (hlen : BERicci.Gamma.IsLengthSpace X)
    (C : ℝ → ℝ≥0) (hC : BoundedOnIntervals C) (h315 : LipContraction m P C)
    (H : ℝ → Measure X → Measure X) (hH : IsDualSemigroup m P H) (h316 : GradBound m H C)
    (f : X → ℝ) (hf : BERicci.Gamma.IsLipB f) (hf0 : ∀ x, 0 ≤ f x)
    (hfsupp : Bornology.IsBounded (Function.support f)) :
    (∀ s : ℝ, 0 ≤ s →
      (∃ K : ℝ≥0, LipschitzWith K (hopfLax s f)) ∧ (∀ x, 0 ≤ hopfLax s f x) ∧
        Bornology.IsBounded (Function.support (hopfLax s f))) ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x y : X,
      Ptilde H t (hopfLax 1 f) x - Ptilde H t f y ≤ (1 / 2) * (C t : ℝ) ^ 2 * dist x y ^ 2 := by sorry

end BERicci.Contract
