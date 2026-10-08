-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_lemma_7_3
-- name    : EkelandVP.Pontryagin.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:27:23.474122+00:00
-- url     : https://prove2.me/theorems/691dbabd-09ca-4093-8f05-dcf827befae7
-- title:
--   Lemma 7.3, p. 349 — the terminal cost u ↦ g(x(T)) is continuous on (𝒰, δ)
-- statement:
--   Assume Ekeland's standing hypotheses of §7: $K$ is a compact metrizable space, $T > 0$, $x_0 \in \mathbb R^n$, $f : \mathbb R^n \times K \times \mathbb R \to \mathbb R^n$ and its state Jacobian $f_x'$ are continuous on $\mathbb R^n \times K \times [0, T]$ (condition (a)), and $\langle x, f(x, u, t)\rangle \le c(1 + \|x\|^2)$ for some constant $c$ (condition (b)). Let $g : \mathbb R^n \to \mathbb R$ be $C^1$.
--
--   Let $(u_k)$ be a sequence of measurable controls and $\bar u$ a measurable control with $\delta(u_k, \bar u) \to 0$, where $\delta(u, v) = \operatorname{meas}\{t \in [0, T] \mid u(t) \neq v(t)\}$. Let $x_k$ be the trajectory of $u_k$ and $\bar x$ the trajectory of $\bar u$. Then
--
--   $$
--   g(x_k(T)) \longrightarrow g(\bar x(T)) \qquad (k \to \infty).
--   $$
--
--   That is, the mapping $F : u \mapsto g(x(T))$, where $x$ is the trajectory corresponding to $u$, is continuous on $(\mathcal U, \delta)$. This is the lower semicontinuity hypothesis needed to apply Ekeland's variational principle to $F$.
--
--   **Formalization Note** Continuity is stated sequentially, which is equivalent on the (pseudo)metric space $(\mathcal U, \delta)$. Trajectories are in integral form (definition `IsTrajectory`). The lemma would hold for $g$ merely continuous; the $C^1$ hypothesis is the section's standing assumption on $g$ and is kept.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), pp. 349–350, Lemma 7.3

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory
import Definitions.Def_EkelandVP_Pontryagin_ctrlDist
open Filter Topology

namespace EkelandVP.Pontryagin

theorem lemma_7_3 {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T) (x₀ : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → K → ℝ → EuclideanSpace ℝ (Fin n))
    (fx : EuclideanSpace ℝ (Fin n) → K → ℝ →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hf : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hfx : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : K), ∀ t ∈ Set.Icc 0 T,
      HasFDerivAt (fun y => f y u t) (fx x u t) x)
    (hfxc : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => fx z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hb : ∃ c : ℝ, ∀ (x : EuclideanSpace ℝ (Fin n)) (u : K), ∀ t ∈ Set.Icc 0 T,
      inner ℝ x (f x u t) ≤ c * (1 + ‖x‖ ^ 2))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 1 g)
    (us : ℕ → ℝ → K) (hus : ∀ k, Measurable (us k)) (ubar : ℝ → K) (hubar : Measurable ubar)
    (hconv : Tendsto (fun k => ctrlDist T (us k) ubar) atTop (𝓝 0))
    (xs : ℕ → ℝ → EuclideanSpace ℝ (Fin n)) (hxs : ∀ k, IsTrajectory f x₀ T (us k) (xs k))
    (xbar : ℝ → EuclideanSpace ℝ (Fin n)) (hxbar : IsTrajectory f x₀ T ubar xbar) :
    Tendsto (fun k => g (xs k T)) atTop (𝓝 (g (xbar T))) := by sorry

end EkelandVP.Pontryagin
