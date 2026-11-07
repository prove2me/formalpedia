-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd
-- name    : FiniteEnergyPlane.exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:39:24.251212+00:00
-- url     : https://prove2.me/theorems/ee3b0b67-9e72-47b3-81ad-b4e0e09f5d6c
-- title:
--   Lower Lipschitz bound on the end of a plane in cylindrical scale
-- statement:
--   Let $u$ converge exponentially fast in $C^\infty$ to the trivial cylinder over a periodic Reeb orbit $P = (x, T)$ at $\infty$, and let $c_0 > 0$ with $c_0 |\tau - \tau'| \le \|x(\tau) - x(\tau')\|$ whenever $|\tau - \tau'| \le T/2$. Then there are $c, R > 0$ such that for all $z, z'$ with $\|z\|, \|z'\| \ge R$,
--   $$c \|z - z'\| \le (1 + \|z\| + \|z'\|) \big( |a(z) - a(z')| + \|w(z) - w(z')\| \big),$$
--   where $a = \mathtt{aCoord}\ H \circ u$ and $w = \mathtt{proj}\ H \circ u$.
--
--   **Role.** Uniform embeddedness of the end of a plane, in the scale of cylindrical coordinates.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` converge exponentially fast in `C^∞` to the trivial cylinder over `P` at `∞`, and let
`x` satisfy `c₀ |τ - τ'| ≤ ‖x τ - x τ'‖` for `|τ - τ'| ≤ T / 2`. Then outside some ball the
symplectization coordinates of `u` satisfy a lower Lipschitz bound in the scale `1 + ‖z‖ + ‖z'‖`. -/
theorem exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (P : ReebOrbit H) (b : ℝ) (hb : 0 < b) (hexp : HasExpAsymptoticsEnd H u cylInf P 1 b)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hsep : ∀ τ τ' : ℝ, |τ - τ'| ≤ P.T / 2 → c₀ * |τ - τ'| ≤ ‖P.x τ - P.x τ'‖) :
    ∃ c > 0, ∃ R > 0, ∀ z z' : ℂ, R ≤ ‖z‖ → R ≤ ‖z'‖ →
      c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
        (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖) := by
  sorry

end FiniteEnergyPlane
