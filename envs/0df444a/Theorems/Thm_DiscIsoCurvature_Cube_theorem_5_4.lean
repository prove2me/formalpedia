-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_5_4
-- name    : DiscIsoCurvature.Cube.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:37.48039+00:00
-- url     : https://prove2.me/theorems/02ef20a8-bc3f-4739-99f3-8636407b43ce
-- title:
--   Theorem 5.4 — Talagrand's L1–L2 inequality (38) and the influence bound (39) under 0-CSGE and LSI
-- statement:
--   There are universal constants $c_1,c_2>0$ with the following property. Let $\mu$ be a distribution on $\{\pm1\}^n$, $q_i>0$ rates reversible for $\mu$, $w$ $b$-bounded weights ($b\in(0,1]$), and suppose 0-CSGE holds with constant $\rho_{\rm csge}$ and LSI with constant $\rho_{\rm lsi}>0$; let $\kappa_0=\max\{-\rho_{\rm csge},0\}$. Then every $f:\Omega\to\mathbb R$ satisfies
--   $$\mathrm{Var}_\mu(f)\le c_1\,\frac{\rho_{\rm lsi}+\kappa_0}{b\,\rho_{\rm lsi}^2}\sum_{i=1}^n\frac{I_{w,i}(f)}{1+\log\big(\sqrt{I_{w,i}(f)}/\mathbb E_\mu[|\delta_{w,i}|f]\big)}\qquad(38)$$
--   (a summand is $0$ when $I_{w,i}(f)=0$) and
--   $$I(f)\ge c_2\,\frac{b^2\rho_{\rm lsi}^2}{\rho_{\rm lsi}+\kappa_0}\,\mathrm{Var}_\mu(f)\Big(1+\log\frac{I_w(f)}{J_w(f)}\Big),\qquad(39)$$
--   with $I(f)$ the unweighted total influence. These give the L1–L2 and KKL inequalities of Theorem 1.1.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - encoding: τ ∈ [0, ∞], t ≥ 0, P_∞ = E_µ → τ : WithTop ℝ≥0, t : ℝ≥0, P_⊤ f = the constant E_µ[f], τ + t computed in WithTop ℝ≥0; reason: Lean's extended half-line; the same instances, with ∞ + t = ∞
--   - reading: unsubscripted ≲ / ≳ in (38) and (39), one constant for each → an explicit ∃ c > 0 quantified before n, µ, q, w, b and the ρ's; reason: the stronger of the two readings; the paper writes ≳_{b,ρcsge} or Ω_b(1) exactly where a constant depends on parameters
--   - encoding: a summand of (38) is zero when I_{w,i}(f) = 0 → if I_{w,i}(f) = 0 then 0 else …; reason: the paper's convention, written out
--   - encoding: I_w(f)/J_w(f) in (39) when f is constant (J_w(f) = 0) → Lean's x/0 = 0 and log 0 = 0; reason: both sides are 0 in that degenerate case, which is the paper's value
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 29, Theorem 5.4

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Theorem 5.4 (Talagrand's L1–L2 inequality; p. 29): there are universal constants
`c₁, c₂ > 0` such that for every `n`, distribution `μ` on `{±1}^n`, positive rates `q`
reversible for `μ`, `b`-bounded weights `w` (`b ∈ (0, 1]`), if 0-CSGE holds with constant
`ρ_csge` and LSI with constant `ρ_lsi > 0`, then for every `f : Ω → ℝ`, with
`κ₀ = max{−ρ_csge, 0}`:
(38) `Var_μ(f) ≤ c₁ ((ρ_lsi + κ₀)/(b ρ_lsi²)) ∑ᵢ I_{w,i}(f)/(1 + log(√(I_{w,i}(f))/E_μ[|δ_{w,i}| f]))`,
a summand being `0` when `I_{w,i}(f) = 0`; and
(39) `I(f) ≥ c₂ (b² ρ_lsi²/(ρ_lsi + κ₀)) Var_μ(f) (1 + log(I_w(f)/J_w(f)))`, `I` unweighted. -/
theorem theorem_5_4 :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (n : ℕ) (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ) (b ρcsge ρlsi : ℝ),
        IsDist μ → IsPositive q → IsReversible μ q → 0 < b → b ≤ 1 → IsBBounded b w →
        CSGEAt μ q w ρcsge 0 → LSI μ q ρlsi →
        ∀ f : BoolCube n → ℝ,
          var μ f ≤ c₁ * ((ρlsi + max (-ρcsge) 0) / (b * ρlsi ^ 2)) *
              ∑ i, (if wInfluenceI μ w q i f = 0 then 0 else
                wInfluenceI μ w q i f /
                  (1 + Real.log (Real.sqrt (wInfluenceI μ w q i f) /
                    expect μ (absDelta w q i f)))) ∧
          c₂ * (b ^ 2 * ρlsi ^ 2 / (ρlsi + max (-ρcsge) 0)) * var μ f *
              (1 + Real.log (wInfluence μ w q f / wSqInfluence μ w q f))
            ≤ wInfluence μ (unitWeight n) q f := by sorry

end DiscIsoCurvature.Cube
