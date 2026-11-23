-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_intervalIntegral
-- name    : FiniteEnergyPlane.contDiffOn_intervalIntegral
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T21:11:54.725008+00:00
-- url     : https://prove2.me/theorems/6cae3c8a-a966-4467-b7f3-53b45e285285
-- title:
--   Parametric interval integrals of C^l functions are C^l on open sets
-- statement:
--   Let $E$ and $G$ be real normed spaces, $O\subseteq E$ open, $l\in\mathbb{N}$, $a,b\in\mathbb{R}$, and $F:E\times\mathbb{R}\to G$ of class $C^l$ on $O\times\mathbb{R}$. Then
--   $$x\mapsto\int_a^bF(x,t)\,dt$$
--   is of class $C^l$ on $O$.
--
--   This is the finite-order form of smoothness of parameter integrals, for a parameter in an open set. It is used for the dependence of energies on parameters in families of planes (Hryniewicz 2012, Lemma 7.3).
--
--   **Formalization Note** $E$ and $G$ are in the same universe. The integral is the interval integral `∫ t in a..b`, and $C^l$ on a set is `ContDiffOn ℝ l`. $E$ need not be finite-dimensional and $G$ need not be complete.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

universe u

/-- If `F` is `C^l` on `O × ℝ` with `O` open, then `x ↦ ∫ t in a..b, F (x, t)` is `C^l` on `O`. -/
theorem contDiffOn_intervalIntegral {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : ℕ) {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] {O : Set E} (hO : IsOpen O)
    {F : E × ℝ → G} (hF : ContDiffOn ℝ l F (O ×ˢ Set.univ)) (a b : ℝ) :
    ContDiffOn ℝ l (fun x => ∫ t in a..b, F (x, t)) O := by
  sorry

end FiniteEnergyPlane
