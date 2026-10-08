-- Prove2me | Theorems.Thm_BERicci_Gamma_lemma_2_1_iii
-- name    : BERicci.Gamma.lemma_2_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:23.83402+00:00
-- url     : https://prove2.me/theorems/09867ef5-92d3-4709-ac5f-5df283ee688c
-- title:
--   Lemma 2.1 (iii), p. 16 — B_t[f;φ] ∈ C⁰((0,t)) and ∂ₛA_t = B_t (2.25), with the extensions to s = t and s = 0
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ with heat flow $(\mathsf P_t)_{t\ge0}$ and generator $\Delta_{\mathcal E}$, as in (2.1). Fix $f\in L^2(X,m)$, $\varphi\in L^2\cap L^\infty(X,m)$ and $t>0$, and let $\mathsf A_t[f;\varphi](s)=\tfrac12\int_X(\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$, $\mathsf A^\Delta_t[f;\varphi](s)=\tfrac12\int_X(\Delta_{\mathcal E}\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$ and $\mathsf B_t[f;\varphi](s)=\Gamma[\mathsf P_{t-s}f;\mathsf P_s\varphi]$.
--
--   Then $\mathsf B_t[f;\varphi](s)$ is defined for $s\in(0,t)$, $s\mapsto\mathsf B_t[f;\varphi](s)$ is continuous on $(0,t)$, and
--
--   $$\frac{\partial}{\partial s}\mathsf A_t[f;\varphi](s)=\mathsf B_t[f;\varphi](s)\qquad\text{for every }s\in(0,t).\tag{2.25}$$
--
--   Moreover (2.25) and the regularity of $\mathsf A$ and $\mathsf B$ extend to $s=t$ if $f\in\mathbb V$, and to $s=0$ if $\varphi\in\mathbb V_\infty$: in the first case $\mathsf B_t$ is defined at $t$, continuous on $(0,t]$, and is the left derivative of $\mathsf A_t$ at $t$; in the second, the same holds at $0$ on $[0,t)$ with the right derivative.
--
--   The identity $\mathsf A'=\mathsf B$ is the first step of the $\Gamma$-calculus along the heat flow that underlies all equivalences of Corollary 2.3.
--
--   **Formalization Note** The heat flow is a binder pinned by `IsHeatSemigroup`; $\Delta_{\mathcal E}\mathsf P_{t-s}f$ is a generator witness, which is unique $m$-a.e., so the values of $\mathsf A^\Delta_t$ do not depend on it. $\Gamma[\cdot;\cdot]$ is the predicate `IsGammaVal` (the extension (2.20)), so "$\mathsf B_t(s)$ is defined" is part of the claim. Strong locality is a standing hypothesis of the section. At the endpoints the derivative is taken within $[0,t]$.
-- source:
--   arXiv:1209.5786v4, Lemma 2.1 (iii), (2.25), p. 16

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- Lemma 2.1 (iii), p. 16: `B_t[f; φ](s) = Γ[P_{t−s} f; P_s φ]` is defined and continuous on `(0,t)`
and is the derivative of `A_t[f; φ]` there (2.25); both extend to `s = t` if `f ∈ 𝕍` and to
`s = 0` if `φ ∈ 𝕍∞`. -/
theorem lemma_2_1_iii
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (hE : IsDirichletForm m E) (hloc : IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : IsHeatSemigroup m E P)
    (f φ : X → ℝ) (hf : MemLp f 2 m) (hφ2 : MemLp φ 2 m) (hφTop : MemLp φ ⊤ m)
    (t : ℝ) (ht : 0 < t) :
    ∃ B : ℝ → ℝ,
      (∀ s ∈ Set.Ioo 0 t, IsGammaVal m E (P (t - s) f) (P (t - s) f) (P s φ) (B s)) ∧
      ContinuousOn B (Set.Ioo 0 t) ∧
      (∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun r => At m P f φ t r) (B s) s) ∧
      (E f < ⊤ →
        IsGammaVal m E (P (t - t) f) (P (t - t) f) (P t φ) (B t) ∧
        ContinuousOn B (Set.Ioc 0 t) ∧
        HasDerivWithinAt (fun r => At m P f φ t r) (B t) (Set.Icc 0 t) t) ∧
      (E φ < ⊤ →
        IsGammaVal m E (P (t - 0) f) (P (t - 0) f) (P 0 φ) (B 0) ∧
        ContinuousOn B (Set.Ico 0 t) ∧
        HasDerivWithinAt (fun r => At m P f φ t r) (B 0) (Set.Icc 0 t) 0) := by sorry

end BERicci.Gamma
