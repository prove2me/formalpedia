-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_fact_4_10
-- name    : DiscIsoCurvature.Cube.fact_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:16.121263+00:00
-- url     : https://prove2.me/theorems/f4ef1eee-7dc0-455c-a2ab-4e50de6e8f16
-- title:
--   Fact 4.10 — 0-CSGE with constant ρ implies WGE and SGE with the same ρ
-- statement:
--   Let $\mu$ be a distribution on $\{\pm1\}^n$, $q_i>0$ rates reversible for $\mu$ and $w_i>0$ weights. If 0-CSGE holds with constant $\rho\in\mathbb R$, i.e. $\|\nabla_wP_tf\|_2\le e^{-\rho t}\|P_t|\nabla_w|f\|_2$ pointwise for all $f$ and $t\ge0$, then both
--   $$\Gamma_w(P_tf)\le e^{-2\rho t}P_t(\Gamma_w(f))\quad\text{and}\quad\sqrt{\Gamma_w(P_tf)}\le e^{-\rho t}P_t\sqrt{\Gamma_w(f)}$$
--   hold for all $f$ and $t\ge0$ (WGE and SGE with constant $\rho$).
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - reading: weight functions w_i : Ω → R+ → IsPositive w: w_i(x) > 0 for all i, x; reason: same notation R+ as for the rates; b-bounded weights are positive in any case
--   - encoding: P_t = e^{tL} → semigroup q t f = (NormedSpace.exp (t • generator q)).mulVec f, generator q the matrix of L on ℝ^Ω; reason: the matrix exponential of the generator on the finite space; same operator
--   - encoding: τ ∈ [0, ∞], t ≥ 0, P_∞ = E_µ → τ : WithTop ℝ≥0, t : ℝ≥0, P_⊤ f = the constant E_µ[f], τ + t computed in WithTop ℝ≥0; reason: Lean's extended half-line; the same instances, with ∞ + t = ∞
--   - encoding: inequalities between functions on Ω → stated at every x ∈ Ω; reason: the paper's convention f ≤ g iff f(x) ≤ g(x) for all x (§4.1)
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 21, Fact 4.10

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Fact 4.10 (p. 21): in the setting of Definition 4.8, if 0-CSGE holds with constant
`ρ ∈ ℝ`, then both WGE and SGE hold with the same constant `ρ`. -/
theorem fact_4_10 {n : ℕ} (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ)
    (hμ : IsDist μ) (hq : IsPositive q) (hrev : IsReversible μ q) (hw : IsPositive w) (ρ : ℝ)
    (h0 : CSGEAt μ q w ρ 0) :
    WGE q w ρ ∧ SGE q w ρ := by sorry

end DiscIsoCurvature.Cube
