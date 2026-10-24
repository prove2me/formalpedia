-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_cutoff
-- name    : FiniteEnergyPlane.exists_cutoff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:06:26.373612+00:00
-- url     : https://prove2.me/theorems/6a5b941d-70aa-4eca-b7b8-e703254558c1
-- title:
--   A $C^1$ nonincreasing cutoff $\varphi:\mathbb{R}\to[0,1]$ equal to $1$ on $(-\infty,1/4]$ and to $0$ on $[3/4,\infty)$
-- statement:
--   There is a $C^1$ function $\varphi:\mathbb{R}\to\mathbb{R}$ such that:
--   - $0\le\varphi\le1$;
--   - $\varphi=1$ on $(-\infty,1/4]$ and $\varphi=0$ on $[3/4,\infty)$;
--   - $\varphi'\le0$ everywhere and $\varphi'=0$ on $(3/4,\infty)$;
--   - $\varphi'$ is bounded.
--
--   Such a profile is used to build radial cutoffs $\varphi(|x|^2/s^2)$ whose derivative in $s$ has a sign.
--
--   **Formalization Note** $\varphi'$ is `deriv φ`. Boundedness is `∃ M, ∀ t, |deriv φ t| ≤ M`.
-- source:
--   Standard; used for the monotonicity lemma, A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Support

namespace FiniteEnergyPlane

open Set Filter Topology

/-- There is a `C¹` function `φ : ℝ → ℝ` with values in `[0, 1]`, equal to `1` on `(-∞, 1/4]`
and to `0` on `[3/4, ∞)`, with `φ' ≤ 0` everywhere, `φ' = 0` on `(3/4, ∞)`, and `φ'` bounded. -/
theorem exists_cutoff : ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ t, t ≤ 1 / 4 → φ t = 1) ∧
    (∀ t, 3 / 4 ≤ t → φ t = 0) ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, deriv φ t ≤ 0) ∧
    (∀ t, 3 / 4 < t → deriv φ t = 0) ∧ ∃ M, ∀ t, |deriv φ t| ≤ M := by
  sorry

end FiniteEnergyPlane
