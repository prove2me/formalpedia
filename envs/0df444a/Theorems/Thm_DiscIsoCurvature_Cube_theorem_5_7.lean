-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_5_7
-- name    : DiscIsoCurvature.Cube.theorem_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:39.837102+00:00
-- url     : https://prove2.me/theorems/38a99367-6dd3-4469-b626-cc2fcec99766
-- title:
--   Theorem 5.7 — Eldan–Gross: A_w(f) ≳_{b,ρ_csge} (√ρ_lsi min{1, ρ_lsi}/√(1 + log₊(1/ρ_lsi))) Var_µ(f) √log(1 + e/J_w(f))
-- statement:
--   For every $b\in(0,1]$ and $\rho_{\rm csge}\in\mathbb R$ there is $c>0$, depending only on $b$ and $\rho_{\rm csge}$, with the following property. Let $\mu$ be a distribution on $\{\pm1\}^n$, $q_i>0$ rates reversible for $\mu$, $w$ $b$-bounded weights, and suppose both 0-CSGE and ∞-CSGE hold with constant $\rho_{\rm csge}$ and LSI holds with constant $\rho_{\rm lsi}>0$. Then every Boolean $f:\Omega\to\{\pm1\}$ satisfies
--   $$A_w(f)\ge c\,\frac{\sqrt{\rho_{\rm lsi}}\min\{1,\rho_{\rm lsi}\}}{\sqrt{1+\log_+(1/\rho_{\rm lsi})}}\,\mathrm{Var}_\mu(f)\sqrt{\log\Big(1+\frac e{J_w(f)}\Big)},$$
--   where $\log_+x=\max\{\log x,0\}$. This is the Eldan–Gross inequality in the curvature setting.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - encoding: τ ∈ [0, ∞], t ≥ 0, P_∞ = E_µ → τ : WithTop ℝ≥0, t : ℝ≥0, P_⊤ f = the constant E_µ[f], τ + t computed in WithTop ℝ≥0; reason: Lean's extended half-line; the same instances, with ∞ + t = ∞
--   - reading: ≳_{b,ρcsge} → ∀ b ∈ (0, 1], ∀ ρ_csge, ∃ c > 0 before n, µ, q, w, ρ_lsi and f; reason: the paper's notation for a constant depending only on b and ρ_csge
--   - encoding: e/J_w(f) when f is constant (J_w(f) = 0) → Lean's x/0 = 0 and log 0 = 0; reason: both sides are 0 in that degenerate case, which is the paper's value
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 31, Theorem 5.7

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Influence
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Theorem 5.7 (Eldan–Gross inequality; p. 31): for every `b ∈ (0, 1]` and `ρ_csge ∈ ℝ` there
is `c > 0` (depending only on `b` and `ρ_csge`) such that for every `n`, distribution `μ` on
`{±1}^n`, positive rates `q` reversible for `μ`, `b`-bounded weights `w`, if 0-CSGE and
∞-CSGE hold with constant `ρ_csge` and LSI with constant `ρ_lsi > 0`, every Boolean `f` satisfies
`A_w(f) ≥ c (√ρ_lsi min{1, ρ_lsi}/√(1 + log₊(1/ρ_lsi))) Var_μ(f) √(log(1 + e/J_w(f)))`,
`log₊ x = max{log x, 0}`. -/
theorem theorem_5_7 :
    ∀ b ρcsge : ℝ, 0 < b → b ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (ρlsi : ℝ),
        IsDist μ → IsPositive q → IsReversible μ q → IsBBounded b w →
        CSGEAt μ q w ρcsge 0 → CSGEAt μ q w ρcsge ⊤ → LSI μ q ρlsi →
        ∀ f : BoolCube n → ℝ, IsBoolean f →
          c * (Real.sqrt ρlsi * min 1 ρlsi / Real.sqrt (1 + max (Real.log (1 / ρlsi)) 0))
              * var μ f * Real.sqrt (Real.log (1 + Real.exp 1 / wSqInfluence μ w q f))
            ≤ wSurfaceArea μ w q f := by sorry

end DiscIsoCurvature.Cube
