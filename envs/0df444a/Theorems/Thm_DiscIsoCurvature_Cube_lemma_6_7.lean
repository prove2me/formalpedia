-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_lemma_6_7
-- name    : DiscIsoCurvature.Cube.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:39.940958+00:00
-- url     : https://prove2.me/theorems/2963459a-5c2d-4c7a-95d9-9cc572d84b12
-- title:
--   Lemma 6.7 — CSGE with constant b − (1+b²)²/(4b³)(‖R‖₂ + ‖R‖₁) when w⋆ ∈ [b, 1/b]
-- statement:
--   Let $\mu$ be a fully supported distribution on $\{\pm1\}^n$ and $R$ its Dobrushin influence matrix (Definition 6.6). If $w^\star_i(x)\in[b,1/b]$ for every $x$ and $i$, then under the canonical rates and weights, CSGE holds for every $\tau\in[0,\infty]$ with constant
--   $$\rho=b-\frac{(1+b^2)^2}{4b^3}\big(\|R\|_2+\|R\|_1\big),$$
--   where $\|R\|_1$ is the maximum column sum and $\|R\|_2$ the spectral norm. This turns Theorem 6.4 into a condition on the Dobrushin matrix.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: τ ∈ [0, ∞], t ≥ 0, P_∞ = E_µ → τ : WithTop ℝ≥0, t : ℝ≥0, P_⊤ f = the constant E_µ[f], τ + t computed in WithTop ℝ≥0; reason: Lean's extended half-line; the same instances, with ∞ + t = ∞
--   - encoding: P_t = e^{tL} → semigroup q t f = (NormedSpace.exp (t • generator q)).mulVec f, generator q the matrix of L on ℝ^Ω; reason: the matrix exponential of the generator on the finite space; same operator
--   - encoding: w⋆_i(x) ∈ [b, 1/b] (b implicit) → IsBBounded b (wStar µ), b any real; reason: for n ≥ 1 the hypothesis forces 0 < b ≤ 1; at n = 0 the empty gradients make CSGE true for every real b
--   - encoding: R of Definition 6.6 on {±1}^n → dobrushinMatrix µ with X = Bool; reason: the definition the lemma cites; on the cube it equals Eq. (6)
--   - generalization: the positive-dimensional canonical cube → also permits n = 0 and arbitrary b in that case; reason: the one-point cube has empty gradient vectors, so both sides of every CSGE inequality are zero; every positive-dimensional source instance is retained
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 37, Lemma 6.7

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature
import Definitions.Def_DiscIsoCurvature_Cube_Dobrushin

namespace DiscIsoCurvature.Cube

/-- Lemma 6.7 (p. 37): for `μ` fully supported on `{±1}^n` with `w⋆ᵢ(x) ∈ [b, 1/b]` for all
`i, x`, CSGE holds (every `τ ∈ [0, ∞]`) under the canonical rates and weights with constant
`ρ = b − ((1 + b²)²/(4b³)) (‖R‖₂ + ‖R‖₁)`, `R` the Dobrushin matrix of Definition 6.6
(`X = Bool`). -/
theorem lemma_6_7 {n : ℕ} (μ : BoolCube n → ℝ) (hμ : IsFullDist μ) (b : ℝ)
    (hb : IsBBounded b (wStar μ)) :
    CSGE μ (qStar μ) (wStar μ)
      (b - ((1 + b ^ 2) ^ 2 / (4 * b ^ 3)) *
        (specNorm (dobrushinMatrix μ) + colSumNorm (dobrushinMatrix μ))) := by sorry

end DiscIsoCurvature.Cube
