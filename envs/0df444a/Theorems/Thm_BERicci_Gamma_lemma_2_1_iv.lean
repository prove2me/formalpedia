-- Prove2me | Theorems.Thm_BERicci_Gamma_lemma_2_1_iv
-- name    : BERicci.Gamma.lemma_2_1_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:38.230173+00:00
-- url     : https://prove2.me/theorems/805bb1f0-d614-4782-bac0-e30ecb9a08de
-- title:
--   Lemma 2.1 (iv), p. 16 — for φ ≥ 0, A_t[f;φ] and A^Δ_t[f;φ] are nondecreasing
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ with heat flow $(\mathsf P_t)_{t\ge0}$ and generator $\Delta_{\mathcal E}$, as in (2.1). Fix $f\in L^2(X,m)$, $\varphi\in L^2\cap L^\infty(X,m)$ and $t>0$, and let $\mathsf A_t[f;\varphi](s)=\tfrac12\int_X(\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$, $\mathsf A^\Delta_t[f;\varphi](s)=\tfrac12\int_X(\Delta_{\mathcal E}\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$ and $\mathsf B_t[f;\varphi](s)=\Gamma[\mathsf P_{t-s}f;\mathsf P_s\varphi]$.
--
--   If $\varphi\ge0$ $m$-a.e., then $s\mapsto\mathsf A_t[f;\varphi](s)$ is nondecreasing on $[0,t]$ and $s\mapsto\mathsf A^\Delta_t[f;\varphi](s)$ is nondecreasing on $[0,t)$.
--
--   Monotonicity of $\mathsf A^\Delta$ is what turns the dimensional term of the integrated estimates (2.30)–(2.31) into the pointwise terms $(\Delta_{\mathcal E}\mathsf P_tf)^2$ of (2.34)–(2.35).
--
--   **Formalization Note** The heat flow is a binder pinned by `IsHeatSemigroup`; $\Delta_{\mathcal E}\mathsf P_{t-s}f$ is a generator witness, which is unique $m$-a.e., so the values of $\mathsf A^\Delta_t$ do not depend on it. $\Gamma[\cdot;\cdot]$ is the predicate `IsGammaVal` (the extension (2.20)), so "$\mathsf B_t(s)$ is defined" is part of the claim. Strong locality is a standing hypothesis of the section.
-- source:
--   arXiv:1209.5786v4, Lemma 2.1 (iv), p. 16

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- Lemma 2.1 (iv), p. 16: for nonnegative `φ`, `s ↦ A_t[f; φ](s)` and `s ↦ A^Δ_t[f; φ](s)` are
nondecreasing. -/
theorem lemma_2_1_iv
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (hE : IsDirichletForm m E) (hloc : IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : IsHeatSemigroup m E P)
    (f φ : X → ℝ) (hf : MemLp f 2 m) (hφ2 : MemLp φ 2 m) (hφTop : MemLp φ ⊤ m)
    (t : ℝ) (ht : 0 < t)
    (hφ0 : 0 ≤ᵐ[m] φ) :
    MonotoneOn (fun s => At m P f φ t s) (Set.Icc 0 t) ∧
      ∃ lap : ℝ → X → ℝ,
        (∀ s ∈ Set.Ico 0 t, IsGenerator m E (P (t - s) f) (lap s)) ∧
        MonotoneOn (fun s => AtLap m P (lap s) φ s) (Set.Ico 0 t) := by sorry

end BERicci.Gamma
