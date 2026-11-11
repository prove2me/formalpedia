-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_6_4
-- name    : DiscIsoCurvature.Cube.theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:22.862398+00:00
-- url     : https://prove2.me/theorems/47741979-fbc6-4647-ac89-97c37f563178
-- title:
--   Theorem 6.4 — CSGE for every τ ∈ [0, ∞] under the canonical rates and weights with ρ = λ_min(D⋆ − diag{M⋆1} − ½(M⋆ + M⋆ᵀ))
-- statement:
--   Let $\mu$ be a fully supported distribution on $\{\pm1\}^n$, with canonical rates $q^\star$ and weights $w^\star$, matrix fields $M$, $D$ of (49), (51), $M^\star=(\sup_x|M_{ij}(x)|)$ and $D^\star=(\inf_xD_{ij}(x))$. Then CSGE holds for every $\tau\in[0,\infty]$ with constant
--   $$\rho=\lambda_{\min}\Big(D^\star-\mathrm{diag}\{M^\star\mathbf1\}-\tfrac12\big(M^\star+(M^\star)^\top\big)\Big).$$
--   That is, for every $\tau\in[0,\infty]$, $f$, $t\ge0$ and $x$: $\|P_\tau|\nabla^\star|P_tf\|_2(x)\le e^{-\rho t}\|P_{\tau+t}|\nabla^\star|f\|_2(x)$. This is the paper's sufficient condition for CSGE.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: τ ∈ [0, ∞], t ≥ 0, P_∞ = E_µ → τ : WithTop ℝ≥0, t : ℝ≥0, P_⊤ f = the constant E_µ[f], τ + t computed in WithTop ℝ≥0; reason: Lean's extended half-line; the same instances, with ∞ + t = ∞
--   - encoding: P_t = e^{tL} → semigroup q t f = (NormedSpace.exp (t • generator q)).mulVec f, generator q the matrix of L on ℝ^Ω; reason: the matrix exponential of the generator on the finite space; same operator
--   - encoding: λ_min of a symmetric matrix → lambdaMin A = inf_{v ≠ 0} vᵀAv/vᵀv; reason: for n ≥ 1 the bounded Rayleigh infimum is the minimum eigenvalue of this symmetric matrix; the zero-dimensional extension is described separately
--   - generalization: minimum eigenvalue for a positive-dimensional symmetric matrix → also permits n = 0, with lambdaMin of the empty matrix defined as 0; reason: there is no eigenvalue in dimension zero, but CSGE there is 0 ≤ 0; every source instance in positive dimension is retained
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 35, Theorem 6.4

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Theorem 6.4 (p. 35): for `μ` fully supported on `{±1}^n`, under the canonical rates `q⋆`
and weights `w⋆`, CSGE holds for every `τ ∈ [0, ∞]` with constant
`ρ = λ_min(D⋆ − diag{M⋆1} − ½(M⋆ + (M⋆)ᵀ))` (55). -/
theorem theorem_6_4 {n : ℕ} (μ : BoolCube n → ℝ) (hμ : IsFullDist μ) :
    CSGE μ (qStar μ) (wStar μ)
      (lambdaMin (matDStar μ - Matrix.diagonal ((matMStar μ).mulVec (fun _ => 1))
        - (1 / 2 : ℝ) • (matMStar μ + Matrix.transpose (matMStar μ)))) := by sorry

end DiscIsoCurvature.Cube
