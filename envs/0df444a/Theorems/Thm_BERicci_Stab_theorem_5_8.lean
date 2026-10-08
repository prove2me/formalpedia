-- Prove2me | Theorems.Thm_BERicci_Stab_theorem_5_8
-- name    : BERicci.Stab.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:24.279975+00:00
-- url     : https://prove2.me/theorems/daf6e7ae-ec85-49e1-a065-7f566d4cd44c
-- title:
--   Theorem 5.8 — BE(K,N) on Riemannian energy measure spaces is stable under SGH convergence
-- statement:
--   Let $(X_n,d_n,m_n,\mathcal E_n)$ be Riemannian energy measure spaces with $m_n\in\mathcal P_2(X_n)$ and a common $\mathrm{BE}(K,N)$ condition. Suppose $(X_n,d_n,m_n)$ converges in the Sturm–Gromov–Hausdorff sense to $(X_\infty,d_\infty,m_\infty)$, and set $\mathcal E_\infty=2\operatorname{Ch}_{m_\infty}$. Then
--
--   $$(X_\infty,d_\infty,m_\infty,\mathcal E_\infty)\text{ is a Riemannian energy measure space satisfying }\mathrm{BE}(K,N).$$
--
--   The result says the same curvature-dimension bound survives a limit of varying metric measure spaces. In particular, the limit Cheeger energy is again a quadratic Dirichlet form.
--
--   **Formalization Note** A single $\nu=1/N\ge0$ is used throughout, including $\nu=0$ for $N=\infty$. The limit measure is assumed to have full support, since Definition 3.6 requires it and the paper warns on p. 63 that an SGH ambient limit may lack it. The BE conclusion is stated for every family $P^\infty$ satisfying the heat-flow characterization of $\mathcal E_\infty$ (it is unique a.e.); the existence of the limit heat flow is not assumed, and no Riemannian or BE property of the limit is assumed.
-- source:
--   arXiv:1209.5786v4, Theorem 5.8, p. 65

import Mathlib
import Definitions.Def_BERicci_Stab_Convergence

namespace BERicci.Stab

open MeasureTheory
open scoped ENNReal

/-- Theorem 5.8, p. 65: stability of the BERicci.Gamma.BE(K,N) condition under SGH convergence. -/
theorem theorem_5_8 (Xn : ℕ → Type) (Xlim : Type)
    [∀ n, MetricSpace (Xn n)] [∀ n, MeasurableSpace (Xn n)]
    [∀ n, BorelSpace (Xn n)] [∀ n, CompleteSpace (Xn n)]
    [∀ n, SecondCountableTopology (Xn n)]
    [MetricSpace Xlim] [MeasurableSpace Xlim] [BorelSpace Xlim]
    [CompleteSpace Xlim] [SecondCountableTopology Xlim]
    (m : ∀ n, Measure (Xn n)) (mlim : Measure Xlim)
    (E : (n : ℕ) → (Xn n → ℝ) → ℝ≥0∞)
    (P : (n : ℕ) → ℝ → (Xn n → ℝ) → Xn n → ℝ)
    (S : ℝ → ℝ) (K ν : ℝ)
    (hS : BERicci.Gamma.IsTruncProfile S)
    (hR : ∀ n, BERicci.Gamma.IsRiemannianEMS (m n) (E n) S)
    (hP : ∀ n, BERicci.Gamma.IsHeatSemigroup (m n) (E n) (P n))
    (hBE : ∀ n, BERicci.Gamma.BE (m n) (E n) (P n) K ν)
    (hSGH : SGHConverges Xn Xlim m mlim)
    (hfull : mlim.IsOpenPosMeasure) :
    BERicci.Gamma.IsRiemannianEMS mlim (limitEnergy mlim) S ∧
      ∀ Plim : ℝ → (Xlim → ℝ) → Xlim → ℝ,
        BERicci.Gamma.IsHeatSemigroup mlim (limitEnergy mlim) Plim →
          BERicci.Gamma.BE mlim (limitEnergy mlim) Plim K ν := by sorry

end BERicci.Stab
