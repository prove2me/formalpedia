-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_ne_top_of_univ_eq_ofReal
-- name    : FiniteEnergyPlane.dlambdaEnergy_ne_top_of_univ_eq_ofReal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:41:57.147067+00:00
-- url     : https://prove2.me/theorems/b9cb4095-d253-4183-8510-b6b8e9e3728a
-- title:
--   Finite total dλ-energy is finite on every set
-- statement:
--   Let $H$ define a level $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ and let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ have total $d\lambda$-energy equal to a real number $T$, i.e. $\int_{\mathbb{C}}u^*d\lambda=T$. Then the $d\lambda$-energy of $u$ on every set $A\subseteq\mathbb{C}$ is finite:
--   $$\int_A u^*d\lambda<\infty .$$
--
--   It allows energies of planes on discs to be compared as real numbers.
--
--   **Formalization Note** The $d\lambda$-energy on $A$ is `dlambdaEnergy H A u`, an `ℝ≥0∞`-valued integral of `ENNReal.ofReal` of the density; "total energy $T$" is `dlambdaEnergy H Set.univ u = ENNReal.ofReal T`, and finiteness is `≠ ⊤`.
-- source:
--   Elementary (dλ-energy bookkeeping), used for Hryniewicz (2012), Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If the total `dλ`-energy of `u : ℂ → V n` is finite, then so is its `dλ`-energy on every set. -/
theorem dlambdaEnergy_ne_top_of_univ_eq_ofReal {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (T : ℝ)
    (htot : dlambdaEnergy H Set.univ u = ENNReal.ofReal T) (s : Set ℂ) :
    dlambdaEnergy H s u ≠ ⊤ := by
  sorry

end FiniteEnergyPlane
