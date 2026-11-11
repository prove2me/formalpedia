-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_corollary_5_2
-- name    : DiscIsoCurvature.Cube.corollary_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:27.211201+00:00
-- url     : https://prove2.me/theorems/c344a727-6879-49ea-b867-f3e20d0ce973
-- title:
--   Corollary 5.2 — A_w(f) ≳ (√b ρ_lsi/√(ρ_lsi + κ)) Var_µ(f) √log(e/Var_µ(f)) under rBE and LSI
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $\mu$ be a distribution on $\{\pm1\}^n$, $q_i>0$ rates reversible for $\mu$, and $w$ $b$-bounded weights, $b\in(0,1]$. Suppose rBE holds with constant $\rho_{\rm rbe}$ and LSI with constant $\rho_{\rm lsi}>0$, and let $\kappa=\max\{0,-\rho_{\rm rbe}\}$. Then every $f:\Omega\to\{0,1\}$ satisfies
--   $$A_w(f)\ \ge\ c\,\frac{\sqrt b\,\rho_{\rm lsi}}{\sqrt{\rho_{\rm lsi}+\kappa}}\;\mathrm{Var}_\mu(f)\sqrt{\log\frac{e}{\mathrm{Var}_\mu(f)}} .$$
--   This is Talagrand's variance–surface-area inequality (33) under curvature and log-Sobolev assumptions.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - reading: unsubscripted ≲ / ≳ in (33) → an explicit ∃ c > 0 quantified before n, µ, q, w, b and the ρ's; reason: the stronger of the two readings; the paper writes ≳_{b,ρcsge} or Ω_b(1) exactly where a constant depends on parameters
--   - encoding: the right side of (33) when Var_µ(f) = 0 (f constant) → Lean's x/0 = 0 and log 0 = 0; reason: both sides are 0 in that degenerate case, which is the paper's value
--   - encoding: f : Ω → {0, 1} → f : Ω → ℝ with f(x) = 0 ∨ f(x) = 1; reason: the same functions
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 27, Corollary 5.2

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Corollary 5.2 (Talagrand's variance–surface-area inequality; p. 27): there is a universal
constant `c > 0` such that for every `n`, distribution `μ` on `{±1}^n`, positive rates `q`
reversible for `μ`, `b`-bounded weights `w` (`b ∈ (0, 1]`), if rBE holds with constant `ρ_rbe`
and LSI with constant `ρ_lsi > 0`, then every `f : Ω → {0, 1}` satisfies
`A_w(f) ≥ c (√b ρ_lsi/√(ρ_lsi + κ)) Var_μ(f) √(log(e/Var_μ(f)))`, `κ = max{0, −ρ_rbe}`. -/
theorem corollary_5_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (b ρrbe ρlsi : ℝ),
        IsDist μ → IsPositive q → IsReversible μ q → 0 < b → b ≤ 1 → IsBBounded b w →
        RBE q w ρrbe → LSI μ q ρlsi →
        ∀ f : BoolCube n → ℝ, (∀ x, f x = 0 ∨ f x = 1) →
          c * (Real.sqrt b * ρlsi / Real.sqrt (ρlsi + max 0 (-ρrbe))) * var μ f
              * Real.sqrt (Real.log (Real.exp 1 / var μ f))
            ≤ wSurfaceArea μ w q f := by sorry

end DiscIsoCurvature.Cube
