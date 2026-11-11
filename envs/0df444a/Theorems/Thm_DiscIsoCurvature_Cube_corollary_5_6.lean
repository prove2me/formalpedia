-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_corollary_5_6
-- name    : DiscIsoCurvature.Cube.corollary_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:36.874613+00:00
-- url     : https://prove2.me/theorems/2fbfd6d4-78d1-4c7e-9a80-08c165cc008c
-- title:
--   Corollary 5.6 — KKL: I_w(f) ≳ b(ρ_lsi²/(ρ_lsi + κ₀)) log(1/M_w(f)) Var_µ(f) (41), and the max-influence bound (42)
-- statement:
--   Let $\mu$ be a distribution on $\{\pm1\}^n$, $q$ rates reversible for $\mu$ and $w$ weights, both $q$ and $w$ $b$-bounded for some $b\in(0,1]$. Suppose 0-CSGE holds with constant $\rho_{\rm csge}$ and LSI with constant $\rho_{\rm lsi}>0$; let $\kappa_0=\max\{-\rho_{\rm csge},0\}$ and $M_w(f)=\max_iI_{w,i}(f)$. For Boolean $f:\Omega\to\{\pm1\}$:
--
--   (41) for every $b\in(0,1]$ there is $c>0$ depending only on $b$ with
--   $$I_w(f)\ge c\,\frac{\rho_{\rm lsi}^2}{\rho_{\rm lsi}+\kappa_0}\,\log\frac1{M_w(f)}\,\mathrm{Var}_\mu(f);$$
--
--   (42) for every $b\in(0,1]$ there is $c_b>0$ depending only on $b$ with
--   $$M_w(f)\ge c_b\,\frac{\rho_{\rm lsi}^2}{(\rho_{\rm lsi}+\kappa_0)n}\,\log\frac{(\rho_{\rm lsi}+\kappa_0)n}{\rho_{\rm lsi}^2}\,\mathrm{Var}_\mu(f).$$
--
--   This is the KKL theorem in the curvature setting.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - encoding: τ ∈ [0, ∞], t ≥ 0, P_∞ = E_µ → τ : WithTop ℝ≥0, t : ℝ≥0, P_⊤ f = the constant E_µ[f], τ + t computed in WithTop ℝ≥0; reason: Lean's extended half-line; the same instances, with ∞ + t = ∞
--   - encoding: the subscripted comparison ≳_b in (41) → ∀ b ∈ (0, 1], ∃ c > 0 before n, µ, q, w, the curvature and LSI constants, and f; reason: the printed b is a subscript on ≳, so the implicit constant depends only on b; it is not a multiplicative factor
--   - reading: Ω_b(1) in (42) → ∀ b ∈ (0, 1], ∃ c_b > 0 before n, µ, q, w, the ρ's and f; reason: the paper's notation for a positive constant depending only on b
--   - encoding: q and w b-bounded → IsBBounded b q and IsBBounded b w, no separate positivity hypothesis; reason: b-boundedness with b > 0 implies positivity
--   - encoding: max_{i∈[n]} I_{w,i}(f) → ⨆ i : Fin n, I_{w,i}(f); reason: a maximum over a finite set; 0 when n = 0, where f is constant and Var_µ(f) = 0
--   - encoding: log(1/M_w(f)) when f is constant (M_w(f) = 0) → Lean's x/0 = 0 and log 0 = 0; reason: both sides are 0 in that degenerate case, which is the paper's value
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 30, Corollary 5.6

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Influence
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Corollary 5.6 (KKL; p. 30). Setting: a distribution `μ` on `{±1}^n`, rates `q` reversible
for `μ`, weights `w`, both `q` and `w` `b`-bounded (`b ∈ (0, 1]`), 0-CSGE with constant
`ρ_csge`, LSI with constant `ρ_lsi > 0`, `κ₀ = max{−ρ_csge, 0}`, `M_w(f) = maxᵢ I_{w,i}(f)`.
(41) For every `b ∈ (0, 1]` there is `c > 0` (depending only on `b`) with
`I_w(f) ≥ c (ρ_lsi²/(ρ_lsi + κ₀)) log(1/M_w(f)) Var_μ(f)` for every Boolean `f`.
(42) For every `b ∈ (0, 1]` there is `c_b > 0` (depending only on `b`) with
`M_w(f) ≥ c_b (ρ_lsi²/((ρ_lsi + κ₀) n)) log((ρ_lsi + κ₀) n/ρ_lsi²) Var_μ(f)`. -/
theorem corollary_5_6 :
    (∀ b : ℝ, 0 < b → b ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (ρcsge ρlsi : ℝ),
        IsDist μ → IsReversible μ q → IsBBounded b q → IsBBounded b w →
        CSGEAt μ q w ρcsge 0 → LSI μ q ρlsi →
        ∀ f : BoolCube n → ℝ, IsBoolean f →
          c * (ρlsi ^ 2 / (ρlsi + max (-ρcsge) 0))
              * Real.log (1 / ⨆ i, wInfluenceI μ w q i f) * var μ f
            ≤ wInfluence μ w q f) ∧
    (∀ b : ℝ, 0 < b → b ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (ρcsge ρlsi : ℝ),
        IsDist μ → IsReversible μ q → IsBBounded b q → IsBBounded b w →
        CSGEAt μ q w ρcsge 0 → LSI μ q ρlsi →
        ∀ f : BoolCube n → ℝ, IsBoolean f →
          c * (ρlsi ^ 2 / ((ρlsi + max (-ρcsge) 0) * n))
              * Real.log ((ρlsi + max (-ρcsge) 0) * n / ρlsi ^ 2) * var μ f
            ≤ ⨆ i, wInfluenceI μ w q i f) := by sorry

end DiscIsoCurvature.Cube
