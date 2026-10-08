-- Prove2me | Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
-- name    : FlowCalculus.compact_supported_flow_preserves_regular_level
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:38:22.276636+00:00
-- url     : https://prove2.me/theorems/49725049-7a34-4a14-a81f-7aea17ca6575
-- title:
--   Complete smooth flow preserving a compact regular level
-- statement:
--   Let $M=F^{-1}(0)\subset\mathbb R^n$ be a compact regular level. Let $X:\mathbb R\times\mathbb R^n\to\mathbb R^n$ be jointly smooth. Assume that one compact spatial set contains the support of every $X_t$, and that $X_t(y)\in\ker DF(y)$ whenever $0\le t\le1$ and $y\in M$. Then there is a jointly smooth family of ambient bijections $\psi_t$, for all real times, satisfying
--
--   $$\psi_0=\mathrm{id},\qquad \partial_t\psi_t(y)=X_t(\psi_t(y)).$$
--
--   For $0\le t\le1$, its restriction to $M$ is an isotopy: it maps $M$ bijectively onto itself and its differential is injective on every tangent space. Moreover,
--
--   $$D\psi_t(y)(T_yM)\subseteq T_{\psi_t(y)}M.$$
--
--   This is the integration stage used in Gray stability, formulated independently of contact forms. Tangency is needed only on $[0,1]\times M$, while uniform spatial support gives complete ambient trajectories at all times.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry II (2006), https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed pp. 14–15, equations (2.1)–(2.2). Generalization of the flow-integration step to any smooth time-dependent tangent vector field with uniformly compact spatial support.

import Definitions.Def_GrayStability_Basic

open scoped ContDiff
open GrayStability

theorem FlowCalculus.compact_supported_flow_preserves_regular_level {n c : ℕ}
    (F : E n → (Fin c → ℝ)) (hF : IsCompactRegularLevel F)
    (X : ℝ → E n → E n)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2))
    (hsupp : ∃ K : Set (E n), IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (htan : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F,
      X t y ∈ tangentSpace F y) :
    ∃ ψ : ℝ → E n → E n,
      ContDiff ℝ ∞ (fun p : ℝ × E n => ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Function.Bijective (ψ t)) ∧
      (∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) ∧
      IsIsotopyOf F ψ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        fderiv ℝ (ψ t) y v ∈ tangentSpace F (ψ t y) := by sorry
