-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_lemma_7_2
-- name    : EkelandVP.Pontryagin.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:27:11.900261+00:00
-- url     : https://prove2.me/theorems/d54a5d54-b3bb-4805-a643-97db0e377ada
-- title:
--   Lemma 7.2, p. 349 — the measurable controls with δ(u₁, u₂) = meas{u₁ ≠ u₂} form a complete metric space
-- statement:
--   Let $K$ be a compact metrizable space with its Borel σ-algebra, let $T > 0$, and let $\mathcal U$ be the set of measurable controls $u : [0, T] \to K$ with
--
--   $$
--   \delta(u_1, u_2) = \operatorname{meas}\{t \in [0, T] \mid u_1(t) \neq u_2(t)\}.
--   $$
--
--   Then $(\mathcal U, \delta)$ is a complete metric space, in the following sense:
--
--   1. (triangle inequality (7.10)) $\delta(u_1, u_2) \le \delta(u_1, u_3) + \delta(u_3, u_2)$ for all measurable $u_1, u_2, u_3$;
--   2. $\delta(u_1, u_2) = 0$ if and only if $u_1 = u_2$ almost everywhere on $[0, T]$;
--   3. (completeness) every sequence $(u_k)$ of measurable controls that is Cauchy for $\delta$ converges for $\delta$ to some measurable control $\bar u$: $\delta(u_k, \bar u) \to 0$.
--
--   Symmetry $\delta(u_1, u_2) = \delta(u_2, u_1)$ and nonnegativity hold by definition.
--
--   Completeness of $(\mathcal U, \delta)$ is what allows Ekeland's variational principle (Theorem 1.1) to be applied to the terminal cost as a function of the control.
--
--   **Formalization Note** Controls are functions $\mathbb R \to K$; only their values on $[0, T]$ enter $\delta$. Since $\delta$ vanishes exactly on controls that agree almost everywhere (item 2), $\mathcal U$ is a metric space on almost-everywhere classes of controls, which is the usual reading of the lemma; this is why item 2 is stated in place of "$\delta(u_1, u_2) = 0 \Rightarrow u_1 = u_2$".
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 349, Lemma 7.2 (metric (7.7), triangle inequality (7.10))

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_ctrlDist
open MeasureTheory Filter Topology

namespace EkelandVP.Pontryagin

theorem lemma_7_2 {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T) :
    (∀ u₁ u₂ u₃ : ℝ → K, Measurable u₁ → Measurable u₂ → Measurable u₃ →
      ctrlDist T u₁ u₂ ≤ ctrlDist T u₁ u₃ + ctrlDist T u₃ u₂) ∧
    (∀ u₁ u₂ : ℝ → K, Measurable u₁ → Measurable u₂ →
      (ctrlDist T u₁ u₂ = 0 ↔ u₁ =ᵐ[volume.restrict (Set.Icc 0 T)] u₂)) ∧
    (∀ us : ℕ → ℝ → K, (∀ k, Measurable (us k)) →
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ctrlDist T (us j) (us k) < η) →
      ∃ ubar : ℝ → K, Measurable ubar ∧
        Tendsto (fun k => ctrlDist T (us k) ubar) atTop (𝓝 0)) := by sorry

end EkelandVP.Pontryagin
