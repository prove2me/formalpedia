-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf
-- name    : FiniteEnergyPlane.exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T20:29:23.045474+00:00
-- url     : https://prove2.me/theorems/0e8dff24-44ac-48ca-bc08-911676b7766f
-- title:
--   $\pi\,\partial_s u$ has no zeros near a nondegenerate puncture at infinity
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $R\in\mathbb{R}$ and let $u$ be a finite-energy $\tilde J$-holomorphic curve on $\{z\in\mathbb{C}:|z|>R\}$. Suppose $\infty$ is a puncture of sign $\varepsilon\in\{\pm1\}$ which is nondegenerate in the sense of Hryniewicz, Definition 2.9, with asymptotic orbit $P$, and suppose that $\Pi=\pi\,\partial_s(\mathrm{pr}\circ u)$ (in the global frame of $\xi$) takes nonzero values at points of arbitrarily large modulus. Then for some $R'$, $\Pi$ has no zero on $\{|z|>R'\}$.
--
--   This is the counterpart at $\infty$ of the statement for a finite puncture: the zeros of $\pi\,du$ cannot accumulate at a nondegenerate puncture at $\infty$.
--
--   **Formalization Note** The puncture condition is `IsNondegenerateEnd H u cylInf P ε` with `ε = 1 ∨ ε = -1`; the orbit $P$ may be degenerate. $\Pi$ is `piDs H u`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4, discussion of formula (14) (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Near a nondegenerate puncture at `∞` (Hryniewicz, Definition 2.9, either sign) of a
finite-energy curve on `{|z| > R}`, if `π ∂ₛu` has nonzero values at arbitrarily large `|z|`, then
it has no zeros at all on some region `{|z| > R'}`. -/
theorem exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (R : ℝ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J {z | R < ‖z‖} u) (P : ReebOrbit H)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylInf P ε)
    (hfreq : ∀ R' : ℝ, ∃ z : ℂ, R' < ‖z‖ ∧ piDs H u z ≠ 0) :
    ∃ R' : ℝ, ∀ z : ℂ, R' < ‖z‖ → piDs H u z ≠ 0 := by
  sorry

end FiniteEnergyPlane
