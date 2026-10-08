-- Prove2me | Theorems.Thm_BERicci_Gamma_lemma_2_1_i_ii
-- name    : BERicci.Gamma.lemma_2_1_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:27.789908+00:00
-- url     : https://prove2.me/theorems/87e891d1-5247-406b-9e4d-53d1cb9eb3b5
-- title:
--   Lemma 2.1 (i)–(ii), pp. 15–16 — A_t[f;φ] ∈ C⁰([0,t]) ∩ C¹((0,t)) and A^Δ_t[f;φ] ∈ C⁰([0,t))
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ with heat flow $(\mathsf P_t)_{t\ge0}$ and generator $\Delta_{\mathcal E}$, as in (2.1). Fix $f\in L^2(X,m)$, $\varphi\in L^2\cap L^\infty(X,m)$ and $t>0$, and let $\mathsf A_t[f;\varphi](s)=\tfrac12\int_X(\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$, $\mathsf A^\Delta_t[f;\varphi](s)=\tfrac12\int_X(\Delta_{\mathcal E}\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$ and $\mathsf B_t[f;\varphi](s)=\Gamma[\mathsf P_{t-s}f;\mathsf P_s\varphi]$.
--
--   Then:
--   1. $s\mapsto\mathsf A_t[f;\varphi](s)$ belongs to $C^0([0,t])\cap C^1((0,t))$;
--   2. $s\mapsto\mathsf A^\Delta_t[f;\varphi](s)$ belongs to $C^0([0,t))$.
--
--   These are the regularity facts that make the distributional form (2.33) of the Bakry–Émery condition meaningful.
--
--   **Formalization Note** The heat flow is a binder pinned by `IsHeatSemigroup`; $\Delta_{\mathcal E}\mathsf P_{t-s}f$ is a generator witness, which is unique $m$-a.e., so the values of $\mathsf A^\Delta_t$ do not depend on it. $\Gamma[\cdot;\cdot]$ is the predicate `IsGammaVal` (the extension (2.20)), so "$\mathsf B_t(s)$ is defined" is part of the claim. Strong locality is a standing hypothesis of the section. $C^1((0,t))$ is stated as the existence of a derivative at every point of $(0,t)$ that is continuous on $(0,t)$.
-- source:
--   arXiv:1209.5786v4, Lemma 2.1 (i)–(ii), pp. 15–16

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- Lemma 2.1 (i)–(ii), pp. 15–16: `s ↦ A_t[f; φ](s)` is in `C⁰([0,t]) ∩ C¹((0,t))` and
`s ↦ A^Δ_t[f; φ](s)` is in `C⁰([0,t))`. -/
theorem lemma_2_1_i_ii
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (hE : IsDirichletForm m E) (hloc : IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : IsHeatSemigroup m E P)
    (f φ : X → ℝ) (hf : MemLp f 2 m) (hφ2 : MemLp φ 2 m) (hφTop : MemLp φ ⊤ m)
    (t : ℝ) (ht : 0 < t) :
    ContinuousOn (fun s => At m P f φ t s) (Set.Icc 0 t) ∧
      (∃ ap : ℝ → ℝ, ContinuousOn ap (Set.Ioo 0 t) ∧
        ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun r => At m P f φ t r) (ap s) s) ∧
      ∃ lap : ℝ → X → ℝ,
        (∀ s ∈ Set.Ico 0 t, IsGenerator m E (P (t - s) f) (lap s)) ∧
        ContinuousOn (fun s => AtLap m P (lap s) φ s) (Set.Ico 0 t) := by sorry

end BERicci.Gamma
