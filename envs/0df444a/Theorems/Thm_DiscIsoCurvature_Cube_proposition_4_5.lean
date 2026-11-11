-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_proposition_4_5
-- name    : DiscIsoCurvature.Cube.proposition_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:29.409857+00:00
-- url     : https://prove2.me/theorems/7b419c66-2f37-4665-b441-7c2b026241b4
-- title:
--   Proposition 4.5 — BE ⇔ WGE and rBE ⇔ SGE with the same constant
-- statement:
--   Let $\mu$ be a distribution on $\{\pm1\}^n$, $q_i>0$ rates reversible for $\mu$ and $w_i>0$ weights. For every $\rho\in\mathbb R$:
--   $$\mathrm{BE}(\rho)\iff\mathrm{WGE}(\rho),\qquad \mathrm{rBE}(\rho)\iff\mathrm{SGE}(\rho).$$
--   That is, $\Gamma_{2;w}\ge\rho\Gamma_w$ is equivalent to $\Gamma_w(P_tf)\le e^{-2\rho t}P_t\Gamma_w(f)$, and $\Gamma_{2;w}(f)-\Gamma(\sqrt{\Gamma_w(f)})\ge\rho\Gamma_w(f)$ is equivalent to $\sqrt{\Gamma_w(P_tf)}\le e^{-\rho t}P_t\sqrt{\Gamma_w(f)}$. This is the discrete Bakry–Émery equivalence between curvature and gradient estimates.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - reading: weight functions w_i : Ω → R+ → IsPositive w: w_i(x) > 0 for all i, x; reason: same notation R+ as for the rates; b-bounded weights are positive in any case
--   - encoding: P_t = e^{tL} → semigroup q t f = (NormedSpace.exp (t • generator q)).mulVec f, generator q the matrix of L on ℝ^Ω; reason: the matrix exponential of the generator on the finite space; same operator
--   - encoding: inequalities between functions on Ω → stated at every x ∈ Ω; reason: the paper's convention f ≤ g iff f(x) ≤ g(x) for all x (§4.1)
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 19, Proposition 4.5

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Proposition 4.5 (p. 19): in the setting of Definitions 4.1 and 4.3, for every `ρ ∈ ℝ`,
BE holds with constant `ρ` iff WGE holds with constant `ρ`, and rBE holds with constant `ρ`
iff SGE holds with constant `ρ`. -/
theorem proposition_4_5 {n : ℕ} (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ)
    (hμ : IsDist μ) (hq : IsPositive q) (hrev : IsReversible μ q) (hw : IsPositive w) (ρ : ℝ) :
    (BE q w ρ ↔ WGE q w ρ) ∧ (RBE q w ρ ↔ SGE q w ρ) := by sorry

end DiscIsoCurvature.Cube
