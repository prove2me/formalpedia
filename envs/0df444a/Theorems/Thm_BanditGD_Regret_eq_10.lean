-- Prove2me | Theorems.Thm_BanditGD_Regret_eq_10
-- name    : BanditGD.Regret.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:28:36.618819+00:00
-- url     : https://prove2.me/theorems/9918f561-950e-4dbd-842a-4e1029908717
-- title:
--   Display (10), p. 9 — expected regret of BGD ≤ RdC√n/δ + 3δLn + 2αCn with L = 2C/(αr)
-- statement:
--   In the setting of the bandit model (§1.2, §1.4): $d\ge1$; $S\subseteq\mathbb R^d$ closed and convex with $r\mathbb B\subseteq S\subseteq R\mathbb B$, $r>0$; $C>0$ and costs $c_1,c_2,\dots$ convex on $S$ with values in $[-C,C]$ on $S$; independent directions $u_1,u_2,\dots$ uniform on the unit sphere; $y_1,y_2,\dots$ the run of $\mathrm{BGD}(\alpha,\delta,\nu)$ and $x_t=y_t+\delta u_t$ the played points. Let $n\ge1$, $\nu=R/(C\sqrt n)$, $\alpha\le1$ and $0<\delta<\alpha r$, and put
--   $$L=\frac{2C}{\alpha r}.$$
--   Then
--   $$\mathbb E\Big[\sum_{t=1}^n c_t(x_t)\Big]-\min_{x\in S}\sum_{t=1}^n c_t(x)\le\frac{RdC\sqrt n}{\delta}+3\delta Ln+2\alpha Cn .$$
--
--   This is the untuned regret bound of BGD, valid for any admissible $\alpha$ and $\delta$; Theorem 1 follows by choosing them, and Theorem 2 reuses it with a direct Lipschitz constant in place of $L$.
--
--   **Formalization Note** $L$ is written out as $2C/(\alpha r)$. The paper's $\delta/r\le\alpha<1$ becomes $\delta<\alpha r$, $\alpha\le1$ (see the smoothed-regret item). Independence of the directions and closedness of $S$ are assumed as there. The minimum is an infimum over $S$.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 9, proof of Theorem 1, display (10)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting
open MeasureTheory
open scoped Pointwise

namespace BanditGD.Regret

theorem eq_10 {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : 1 ≤ n) (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : 0 < δ) (hδα : δ < α * r) (hα1 : α ≤ 1)
    (hrun : ∀ ω, IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω)) :
    RegretBandits.Nonlinear.pseudoRegret S c P (fun t ω => y t ω + δ • u t ω) n
      ≤ R * d * C * Real.sqrt n / δ + 3 * δ * (2 * C / (α * r)) * n + 2 * α * C * n := by sorry

end BanditGD.Regret
