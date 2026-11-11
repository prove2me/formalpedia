-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_5_1
-- name    : DiscIsoCurvature.Cube.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:44.775008+00:00
-- url     : https://prove2.me/theorems/d0b98020-56ab-4309-8b4e-d4ad9742993d
-- title:
--   Theorem 5.1 — local Bobkov inequality I(P_t f) ≤ P_t √(I(f)² + γ(t)Γ_w(f)) under rBE
-- statement:
--   Let $\mu$ be a distribution on $\{\pm1\}^n$, $q_i>0$ rates reversible for $\mu$, and $w$ weights that are $b$-bounded for some $b\in(0,1]$. If the reinforced Bakry–Émery condition holds with constant $\rho\in\mathbb R$, then for every $f:\Omega\to[0,1]$, $t\ge0$ and $x$,
--   $$\mathcal I(P_tf)(x)\le P_t\Big(\sqrt{\mathcal I(f)^2+\gamma(t)\,\Gamma_w(f)}\Big)(x),\qquad \gamma(t)=\begin{cases}\dfrac{2(1-e^{-2\rho t})}{b\rho},&\rho\ne0,\\[4pt]\dfrac{4t}{b},&\rho=0,\end{cases}$$
--   with $\mathcal I$ the Gaussian isoperimetric profile. It is the semigroup form of Bobkov's inequality and gives the variance–surface-area inequality.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - encoding: P_t = e^{tL} → semigroup q t f = (NormedSpace.exp (t • generator q)).mulVec f, generator q the matrix of L on ℝ^Ω; reason: the matrix exponential of the generator on the finite space; same operator
--   - encoding: inequalities between functions on Ω → stated at every x ∈ Ω; reason: the paper's convention f ≤ g iff f(x) ≤ g(x) for all x (§4.1)
--   - encoding: f : Ω → [0, 1] → f : Ω → ℝ with 0 ≤ f(x) ≤ 1 for all x; reason: the same functions
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 25, Theorem 5.1

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature
import Definitions.Def_DiscIsoCurvature_Cube_GaussProfile

namespace DiscIsoCurvature.Cube

/-- Theorem 5.1 (local Bobkov inequality; p. 25): for a distribution `μ` on `{±1}^n`, positive
rates `q` reversible for `μ`, `b`-bounded weights `w` (`b ∈ (0, 1]`), if rBE holds with
constant `ρ ∈ ℝ`, then for every `f : Ω → [0, 1]`, `t ≥ 0` and `x`,
`I(P_t f)(x) ≤ P_t √(I(f)² + γ(t) Γ_w(f))(x)`, where `γ(t) = 2(1 − e^{−2ρt})/(bρ)` if `ρ ≠ 0`
and `γ(t) = 4t/b` if `ρ = 0`. -/
theorem theorem_5_1 {n : ℕ} (μ : BoolCube n → ℝ) (q w : Fin n → BoolCube n → ℝ)
    (hμ : IsDist μ) (hq : IsPositive q) (hrev : IsReversible μ q) (b : ℝ) (hb0 : 0 < b)
    (hb1 : b ≤ 1) (hw : IsBBounded b w) (ρ : ℝ) (hrbe : RBE q w ρ) (f : BoolCube n → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (t : ℝ) (ht : 0 ≤ t) (x : BoolCube n) :
    gaussProfile (semigroup q t f x) ≤
      semigroup q t
        (fun y => Real.sqrt (gaussProfile (f y) ^ 2 +
          (if ρ ≠ 0 then 2 * (1 - Real.exp (-2 * ρ * t)) / (b * ρ) else 4 * t / b)
            * gamma w q f f y)) x := by sorry

end DiscIsoCurvature.Cube
