-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_shiftA
-- name    : FiniteEnergyPlane.isNondegenerateEnd_shiftA
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T10:48:36.661202+00:00
-- url     : https://prove2.me/theorems/44e8af55-977d-4027-ba92-0728b3f329c2
-- title:
--   Translations preserve nondegenerate ends of finite-energy curves
-- statement:
--   Let $S = H^{-1}(1) \subset V_n$ be a strictly star-shaped level, let $P$ be a periodic Reeb orbit on $S$, let $e$ be an end and $\varepsilon \in \mathbb{R}$ a sign. If $u : \mathbb{C} \to V_n \setminus \{0\}$ has a nondegenerate end along $e$ asymptotic to $P$ with sign $\varepsilon$ (Hryniewicz, Definition 2.9 (1), (2), (4)), then so does the translated map $c \cdot u = e^{2c} u$ for every $c \in \mathbb{R}$.
--
--   Translations in the $\mathbb{R}$-direction of the symplectization act on $V_n \setminus \{0\} \cong \mathbb{R} \times S$ by radial scaling, and this statement records that this action preserves the asymptotic condition.
--
--   Formalization Note: `shiftA c u` is the map $z \mapsto e^{2c} \bullet u(z)$. The hypothesis `hu` says that $u$ avoids the origin, so that $u$ takes values in the symplectization.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Remark 3.10 and Definition 2.14

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The nondegeneracy of an end is invariant under translations in the `ℝ`-direction of the
symplectization: if `u` avoids `0` and `u` is asymptotic to `P` along the end `e` with sign `ε` in
the sense of Hryniewicz, Definition 2.9, then so is `c · u` for every `c : ℝ`. -/
theorem isNondegenerateEnd_shiftA {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (hu : ∀ z, u z ≠ 0) (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε : ℝ)
    (h : IsNondegenerateEnd H u e P ε) (c : ℝ) :
    IsNondegenerateEnd H (shiftA c u) e P ε := by
  sorry

end FiniteEnergyPlane
