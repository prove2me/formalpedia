-- Prove2me | Theorems.Thm_BERicci_Gamma_lemma_2_1_v
-- name    : BERicci.Gamma.lemma_2_1_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:24.720907+00:00
-- url     : https://prove2.me/theorems/e908dac4-4c7d-473a-ba19-eb4c2c39b6b2
-- title:
--   Lemma 2.1 (v), p. 16 — if Δφ ∈ L² ∩ L∞, C_t ∈ C⁰([0,t)), B_t ∈ C¹([0,t)) with ∂ₛB = 2C (2.26), A_t ∈ C²([0,t))
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ with heat flow $(\mathsf P_t)_{t\ge0}$ and generator $\Delta_{\mathcal E}$, as in (2.1). Fix $f\in L^2(X,m)$, $\varphi\in L^2\cap L^\infty(X,m)$ and $t>0$, and let $\mathsf A_t[f;\varphi](s)=\tfrac12\int_X(\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$, $\mathsf A^\Delta_t[f;\varphi](s)=\tfrac12\int_X(\Delta_{\mathcal E}\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$ and $\mathsf B_t[f;\varphi](s)=\Gamma[\mathsf P_{t-s}f;\mathsf P_s\varphi]$. Assume moreover that $\varphi\in D(\Delta_{\mathcal E})$ with $\Delta_{\mathcal E}\varphi\in L^2\cap L^\infty(X,m)$, and let $\mathsf C_t[f;\varphi](s)=\Gamma_2[\mathsf P_{t-s}f;\mathsf P_s\varphi]$.
--
--   Then $\mathsf C$ belongs to $C^0([0,t))$, $\mathsf B$ belongs to $C^1([0,t))$, and
--
--   $$\frac{\partial}{\partial s}\mathsf B_t[f;\varphi](s)=2\,\mathsf C_t[f;\varphi](s)\qquad\text{for every }s\in[0,t).\tag{2.26}$$
--
--   In particular $\mathsf A\in C^2([0,t))$, with $\mathsf A'=\mathsf B$ and $\mathsf A''=2\mathsf C$.
--
--   This is the identity $\mathsf A''=2\Gamma_2$ along the heat flow, which links the pointwise condition (i) of Corollary 2.3 to the weak condition (iii).
--
--   **Formalization Note** The heat flow is a binder pinned by `IsHeatSemigroup`; $\Delta_{\mathcal E}\mathsf P_{t-s}f$ is a generator witness, which is unique $m$-a.e., so the values of $\mathsf A^\Delta_t$ do not depend on it. $\Gamma[\cdot;\cdot]$ is the predicate `IsGammaVal` (the extension (2.20)), so "$\mathsf B_t(s)$ is defined" is part of the claim. Strong locality is a standing hypothesis of the section. $\Gamma_2$ is the predicate `IsGamma2Val`. The statement asserts that $\mathsf C_t(s)$ is defined for $s\in(0,t)$; at $s=0$, $\Gamma_2[\mathsf P_tf;\varphi]$ requires $\Gamma[\mathsf P_tf;\Delta_{\mathcal E}\varphi]$ with $\Delta_{\mathcal E}\varphi$ possibly outside $\mathbb V$, so the statement says that $\mathsf C(0)$ equals $\Gamma_2[\mathsf P_tf;\varphi]$ whenever the latter is defined. Derivatives on $[0,t)$ are one-sided at $0$.
-- source:
--   arXiv:1209.5786v4, Lemma 2.1 (v), (2.26), p. 16

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- Lemma 2.1 (v), p. 16: if `Δ_E φ ∈ L² ∩ L∞`, then `C_t[f; φ] = Γ₂[P_{t−s} f; P_s φ]` is in
`C⁰([0,t))`, `B_t[f; φ]` is in `C¹([0,t))` with `∂_s B = 2C` (2.26), and `A_t[f; φ] ∈ C²([0,t))`. -/
theorem lemma_2_1_v
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (hE : IsDirichletForm m E) (hloc : IsStronglyLocal m E)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : IsHeatSemigroup m E P)
    (f φ : X → ℝ) (hf : MemLp f 2 m) (hφ2 : MemLp φ 2 m) (hφTop : MemLp φ ⊤ m)
    (t : ℝ) (ht : 0 < t)
    (lφ : X → ℝ) (hlφ : IsGenerator m E φ lφ) (hlφTop : MemLp lφ ⊤ m) :
    ∃ B C : ℝ → ℝ,
      (∀ s ∈ Set.Ico 0 t, IsGammaVal m E (P (t - s) f) (P (t - s) f) (P s φ) (B s)) ∧
      (∀ s ∈ Set.Ioo 0 t, IsGamma2Val m E (P (t - s) f) (P s φ) (C s)) ∧
      (∀ c : ℝ, IsGamma2Val m E (P (t - 0) f) (P 0 φ) c → C 0 = c) ∧
      ContinuousOn C (Set.Ico 0 t) ∧ ContinuousOn B (Set.Ico 0 t) ∧
      (∀ s ∈ Set.Ico 0 t, HasDerivWithinAt B (2 * C s) (Set.Ico 0 t) s) ∧
      ∀ s ∈ Set.Ico 0 t,
        HasDerivWithinAt (fun r => At m P f φ t r) (B s) (Set.Ico 0 t) s := by sorry

end BERicci.Gamma
