-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_corollary_6_9
-- name    : DiscIsoCurvature.Cube.corollary_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:08:23.459248+00:00
-- url     : https://prove2.me/theorems/bf4a25ff-2b60-4292-b18e-ad6cac062882
-- title:
--   Corollary 6.9 — LSI with constant b²(1 − ‖R‖₂)²/(1 + b²) for the canonical rates q⋆
-- statement:
--   Let $n\ge1$ and let $\mu$ be a fully supported distribution on $\{\pm1\}^n$ with $\|R\|_2<1$ ($R$ of Definition 6.6) and $w^\star_i(x)\in[b,1/b]$ for every $x$, $i$. Then the log-Sobolev inequality holds for the canonical rates $q^\star$ with constant
--   $$\rho=\frac{b^2(1-\|R\|_2)^2}{1+b^2},$$
--   that is, $\rho>0$ and $\mathrm{Ent}_\mu[f^2]\le\frac2\rho\mathbb E_\mu[\Gamma(f)]$ for every $f$, with $\Gamma$ the unweighted carré du champ of $q^\star$. It supplies the log-Sobolev hypothesis of §5 under the Dobrushin condition.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: w⋆_i(x) ∈ [b, 1/b] (b implicit) → IsBBounded b (wStar µ), b any real; reason: for n ≥ 1, positivity of w⋆ and its upper bound by 1/b force 0 < b ≤ 1
--   - encoding: R of Definition 6.6 on {±1}^n → dobrushinMatrix µ with X = Bool; reason: the definition the corollary cites; on the cube it equals Eq. (6)
--   - encoding: LSI holds with constant ρ → LSI µ q⋆ ρ, which includes ρ > 0; reason: Definition 3.13 defines LSI for constants ρ > 0
--   - encoding: positive dimension in the Gibbs-sampler setting (Theorem 6.8 has 1/n and a minimum over coordinates) → hypothesis 1 ≤ n; reason: makes the inherited dimension convention explicit; at n = 0 the marginal bounds are vacuous and would allow b = 0, contradicting positivity in the LSI conclusion
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 38, Corollary 6.9

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Dobrushin

namespace DiscIsoCurvature.Cube

/-- Corollary 6.9 (p. 38): for `n ≥ 1` and `μ` fully supported on `{±1}^n` with `‖R‖₂ < 1` (`R` of
Definition 6.6, `X = Bool`) and `w⋆ᵢ(x) ∈ [b, 1/b]` for all `i, x`, the log-Sobolev inequality
holds for the canonical rates `q⋆` with constant `b²(1 − ‖R‖₂)²/(1 + b²)`. -/
theorem corollary_6_9 {n : ℕ} (hn : 1 ≤ n) (μ : BoolCube n → ℝ) (hμ : IsFullDist μ) (b : ℝ)
    (hR : specNorm (dobrushinMatrix μ) < 1) (hb : IsBBounded b (wStar μ)) :
    LSI μ (qStar μ) (b ^ 2 * (1 - specNorm (dobrushinMatrix μ)) ^ 2 / (1 + b ^ 2)) := by sorry

end DiscIsoCurvature.Cube
