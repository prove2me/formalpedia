-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_of_comp_eq_shift
-- name    : FiniteEnergyPlane.isNondegenerateEnd_of_comp_eq_shift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:32:12.646371+00:00
-- url     : https://prove2.me/theorems/998a86de-b400-4edf-8c40-c649e4088796
-- title:
--   Nondegenerate ends are unaffected by a shift of the cylinder coordinate
-- statement:
--   Let $e,e':\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ be cylindrical parametrizations of ends, and let $w,w':\mathbb{C}\to\mathbb{R}^{2n+2}$ satisfy $w'(e(s,t))=w(e'(s+\ell,t))$ for all $s,t$ and some constant $\ell$. If $w'$ is nondegenerately asymptotic along $e$ to a periodic Reeb orbit $P$ with sign $\varepsilon$, then so is $w$ along $e'$.
--
--   This covers the passage between a puncture on the unit disk and the same puncture on a disk of another radius, in the direction opposite to the published statement about affine changes of coordinates.
--
--   **Formalization Note** The asymptotics are `IsNondegenerateEnd H w e P ε`, whose data $d$, $c$, $b$ are existential; $\ell$ is any real number.
-- source:
--   Auxiliary to U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Nondegeneracy of an end does not depend on a shift of the cylinder coordinate: if
`w'(e(s, t)) = w(e'(s + ℓ, t))` for all `s, t`, and `w'` is nondegenerately asymptotic to `P` with sign
`ε` along `e`, then `w` is nondegenerately asymptotic to `P` with sign `ε` along `e'`. -/
theorem isNondegenerateEnd_of_comp_eq_shift {n : ℕ} (H : V n → ℝ) (w w' : ℂ → V n)
    (e e' : ℝ → ℝ → ℂ) (ℓ : ℝ) (he : ∀ s t, w' (e s t) = w (e' (s + ℓ) t)) (P : ReebOrbit H) (ε : ℝ)
    (h : IsNondegenerateEnd H w' e P ε) : IsNondegenerateEnd H w e' P ε := by
  sorry

end FiniteEnergyPlane
