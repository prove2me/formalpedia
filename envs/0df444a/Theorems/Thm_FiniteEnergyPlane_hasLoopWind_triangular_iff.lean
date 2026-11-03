-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_triangular_iff
-- name    : FiniteEnergyPlane.hasLoopWind_triangular_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T15:09:27.734993+00:00
-- url     : https://prove2.me/theorems/7910d6c9-2f86-4b69-92e1-62d76884b476
-- title:
--   Winding numbers are invariant under an upper-triangular loop with positive diagonal
-- statement:
--   Let $a,b,d:\mathbb{R}\to\mathbb{R}$ be continuous and $1$-periodic with $a(t)>0$ and $d(t)>0$ for all $t$, and let $z:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a continuous $1$-periodic loop. Write $z=q+ip$ and let $M(t)=\begin{pmatrix}a(t)&b(t)\\0&d(t)\end{pmatrix}$ act on $\mathbb{C}=\mathbb{R}^2$. Then for every $k\in\mathbb{Z}$, the loop $t\mapsto M(t)z(t)=(a q+b p)+i\,d p$ has winding number $k$ if and only if $z$ has winding number $k$.
--
--   This compares winding numbers of a loop read in two frames that differ by an upper-triangular change of basis with positive diagonal, e.g. a unitary frame of a contact plane and a fixed global frame.
--
--   **Formalization Note** Winding numbers are the predicate `HasLoopWind f k` of `FiniteEnergyPlane_Winding`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Remark 2.6 and Remark 2.13 (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- An upper-triangular loop of real `2 × 2` matrices with positive diagonal, `[[a, b], [0, d]]`
with `a, d > 0`, acting on `ℂ = ℝ²` (`q + i p ↦ (a q + b p) + i d p`), preserves winding numbers
of loops in `ℂ \ {0}`. -/
theorem hasLoopWind_triangular_iff {a b d : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hd : Continuous d) (hap : Function.Periodic a 1) (hbp : Function.Periodic b 1)
    (hdp : Function.Periodic d 1) (ha0 : ∀ t, 0 < a t) (hd0 : ∀ t, 0 < d t) {z : ℝ → ℂ}
    (hz : Continuous z) (hzp : Function.Periodic z 1) (hz0 : ∀ t, z t ≠ 0) (k : ℤ) :
    HasLoopWind (fun t => ((a t * (z t).re + b t * (z t).im : ℝ) : ℂ) +
        ((d t * (z t).im : ℝ) : ℂ) * Complex.I) k ↔ HasLoopWind z k := by
  sorry

end FiniteEnergyPlane
