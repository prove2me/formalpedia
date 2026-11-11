-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_3_16
-- name    : DiscIsoCurvature.Cube.theorem_3_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:08:26.590667+00:00
-- url     : https://prove2.me/theorems/d9ee32c4-1342-4884-9536-974e88824604
-- title:
--   Theorem 3.16 — hypercontractivity ‖P_t f‖_{q,µ} ≤ ‖f‖_{p,µ} when (q − 1)/(p − 1) ≤ e^{2ρt}, from LSI with constant ρ
-- statement:
--   Let $\mu$ be a distribution on $\{\pm1\}^n$ and $q_i>0$ rates reversible for $\mu$, with semigroup $P_t=e^{tL}$. If the log-Sobolev inequality holds with constant $\rho>0$ and $1<p\le r<\infty$ satisfy $\frac{r-1}{p-1}\le e^{2\rho t}$, then for every $f:\Omega\to\mathbb R$
--   $$\|P_tf\|_{r,\mu}\le\|f\|_{p,\mu}.$$
--   (The paper calls the larger exponent $q$; in Lean it is $r$, since $q$ names the rates.) Gross's theorem; §5 uses it to gain the logarithmic factors.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: µ a distribution supported on Ω → IsDist µ: µ(x) ≥ 0 and ∑ₓ µ(x) = 1; reason: with positive rates reversible for µ on the connected cube, µ(x) > 0 for every x follows, so the class of µ is the paper's
--   - reading: transition rates q_i : Ω → R+ → IsPositive q: q_i(x) > 0 for all i, x; reason: the paper writes R+ for positive values and R≥0 for nonnegative ones (Definition 3.17, Lemma 3.6, Definition 3.15)
--   - encoding: P_t = e^{tL} → semigroup q t f = (NormedSpace.exp (t • generator q)).mulVec f, generator q the matrix of L on ℝ^Ω; reason: the matrix exponential of the generator on the finite space; same operator
--   - encoding: exponents p, q → p, r; reason: q names the transition rates in the Lean statement
--   - encoding: t ≥ 0 (P_t defined for t ≥ 0) → t : ℝ with no sign hypothesis; reason: (r − 1)/(p − 1) ≥ 1 and ρ > 0 force t ≥ 0, so no instance is added
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 17, Theorem 3.16

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup

namespace DiscIsoCurvature.Cube

/-- Theorem 3.16 (hypercontractivity; p. 17): in the setting of §3.1 (a distribution `μ` on
`{±1}^n`, positive rates `q` reversible for `μ`), if the log-Sobolev inequality holds with
constant `ρ > 0` and `1 < p ≤ r < ∞` satisfy `(r − 1)/(p − 1) ≤ e^{2ρt}`, then
`‖P_t f‖_{r,μ} ≤ ‖f‖_{p,μ}` for all `f` (`r` is the paper's `q`). -/
theorem theorem_3_16 {n : ℕ} (μ : BoolCube n → ℝ) (q : Fin n → BoolCube n → ℝ)
    (hμ : IsDist μ) (hq : IsPositive q) (hrev : IsReversible μ q) (ρ : ℝ) (hlsi : LSI μ q ρ)
    (p r t : ℝ) (hp : 1 < p) (hpr : p ≤ r) (hexp : (r - 1) / (p - 1) ≤ Real.exp (2 * ρ * t))
    (f : BoolCube n → ℝ) :
    lpNorm μ r (semigroup q t f) ≤ lpNorm μ p f := by sorry

end DiscIsoCurvature.Cube
