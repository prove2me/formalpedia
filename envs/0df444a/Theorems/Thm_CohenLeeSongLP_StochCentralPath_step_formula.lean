-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_step_formula
-- name    : CohenLeeSongLP.StochCentralPath.step_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:26:44.352377+00:00
-- url     : https://prove2.me/theorems/3202fbdf-27ae-4b2d-b7ea-2ddef4ab7ab3
-- title:
--   Lemma 4.2 — explicit formula (11)–(13) for the step of StochasticStep
-- statement:
--   In the paper's setting $n\ge10$, let $A\in\mathbb R^{d\times n}$ have full row rank $d$, let $x,s,\widetilde v\in\mathbb R^n$ be positive, with $x/s\approx_{\epsilon_{\mathrm{mp}}}\widetilde v$ and $0<\epsilon_{\mathrm{mp}}\le1/40000$, and let $\overline x,\overline s$, $\overline P$ and $\widetilde\delta_x,\widetilde\delta_s$ be as computed by StochasticStep (lines 3 and 9–11 of Algorithm 1). Then for every vector $\widetilde\delta_\mu\in\mathbb R^n$,
--   $$\widetilde\delta_x=\frac{\overline X}{\sqrt{\overline X\,\overline S}}(I-\overline P)\frac{1}{\sqrt{\overline X\,\overline S}}\widetilde\delta_\mu,\qquad(11)$$
--   $$\widetilde\delta_s=\frac{\overline S}{\sqrt{\overline X\,\overline S}}\overline P\frac{1}{\sqrt{\overline X\,\overline S}}\widetilde\delta_\mu,\qquad(12)$$
--   with $\overline P=\sqrt{\overline X/\overline S}\,A^\top\big(A\frac{\overline X}{\overline S}A^\top\big)^{-1}A\sqrt{\overline X/\overline S}$ (13), and there is $\widetilde\delta_y\in\mathbb R^d$ such that system (7) holds:
--   $$\overline X\widetilde\delta_s+\overline S\widetilde\delta_x=\widetilde\delta_\mu,\qquad A\widetilde\delta_x=0,\qquad A^\top\widetilde\delta_y+\widetilde\delta_s=0.$$
--   Moreover $\overline P$ is an orthogonal projection: $\overline P^2=\overline P=\overline P^\top$ (§3, p. 3:7).
--
--   This is the explicit form of the step used in every subsequent calculation of §4.
--
--   **Formalization Note** $\overline X,\overline S$ are diagonal matrices and the inverse is Mathlib's matrix inverse. The projection property is asserted in §3 without a number and is included because Claim 4.5 uses it.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:10, Lemma 4.2, Eqs. (11)–(13); p. 3:5, system (7); p. 3:7, §3 (P̄ is an orthogonal projection)

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

open Matrix

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma 4.2 (p. 3:10): for the section's `n ≥ 10`, positive `x, s, ṽ`, an update
`x/s ≈_{ε_mp} ṽ` with `0 < ε_mp ≤ 1/40000`, and a full-row-rank `A`, the vectors
`δ̃_x, δ̃_s` computed by lines 9–11 of StochasticStep from any `δ̃_μ` satisfy
(11) `δ̃_x = (X̄/√(X̄S̄))(I − P̄)(1/√(X̄S̄)) δ̃_μ` and (12) `δ̃_s = (S̄/√(X̄S̄)) P̄ (1/√(X̄S̄)) δ̃_μ`,
and solve system (7): `X̄δ̃_s + S̄δ̃_x = δ̃_μ`, `Aδ̃_x = 0`, `Aᵀδ̃_y + δ̃_s = 0` for some `δ̃_y`.
Moreover `P̄` of (13) is an orthogonal projection (§3, p. 3:7). -/
theorem step_formula {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x s v : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) (hv : ∀ i, 0 < v i)
    (εmp : ℝ) (hεmp : 0 < εmp ∧ εmp ≤ 1 / 40000)
    (hw : ApproxVec εmp (fun i => x i / s i) v)
    (δ : Fin n → ℝ) :
    stepX A x s v δ =
      (diagonal (fun i => xbar x s v i / Real.sqrt (xbar x s v i * sbar x s v i)) *
        (1 - projBar A (xbar x s v) (sbar x s v)) *
        diagonal (fun i => 1 / Real.sqrt (xbar x s v i * sbar x s v i))) *ᵥ δ ∧
    stepS A x s v δ =
      (diagonal (fun i => sbar x s v i / Real.sqrt (xbar x s v i * sbar x s v i)) *
        projBar A (xbar x s v) (sbar x s v) *
        diagonal (fun i => 1 / Real.sqrt (xbar x s v i * sbar x s v i))) *ᵥ δ ∧
    (∃ δy : Fin d → ℝ,
      (∀ i, xbar x s v i * stepS A x s v δ i + sbar x s v i * stepX A x s v δ i = δ i) ∧
      A *ᵥ stepX A x s v δ = 0 ∧
      Aᵀ *ᵥ δy + stepS A x s v δ = 0) ∧
    projBar A (xbar x s v) (sbar x s v) * projBar A (xbar x s v) (sbar x s v) =
      projBar A (xbar x s v) (sbar x s v) ∧
    (projBar A (xbar x s v) (sbar x s v))ᵀ = projBar A (xbar x s v) (sbar x s v) := by sorry

end CohenLeeSongLP.StochCentralPath
