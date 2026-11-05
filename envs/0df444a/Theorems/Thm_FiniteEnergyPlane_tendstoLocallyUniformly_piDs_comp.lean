-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoLocallyUniformly_piDs_comp
-- name    : FiniteEnergyPlane.tendstoLocallyUniformly_piDs_comp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:36:32.945005+00:00
-- url     : https://prove2.me/theorems/1010937e-6ce1-4801-a353-50b721b8ff00
-- title:
--   $\pi\partial_s$ of rescaled planes converges along curves under $C^\infty_{\mathrm{loc}}$ convergence
-- statement:
--   Let $u_k$ be finite-energy $\tilde J$-holomorphic planes in the symplectization of a strictly star-shaped level $S\subset\mathbb{R}^4$, let $c_k>0$, and suppose $c_ku_k\to w$ in $C^\infty_{\mathrm{loc}}(U)$ with $w$ a finite-energy $\tilde J$-holomorphic curve on an open set $U\subseteq\mathbb{C}$. If $L:\mathbb{R}\to\mathbb{C}$ is continuous with image in a compact subset of $U$, then $\pi\,\partial_s\mathrm{pr}(u_k)\circ L\to\pi\,\partial_s\mathrm{pr}(w)\circ L$ locally uniformly on $\mathbb{R}$.
--
--   Winding numbers of the $\xi$-component of a limit are compared with those of the sequence through this statement.
--
--   **Formalization Note** The functions are `piDs H (u k) (L t)` with values in $\mathbb{C}$, through the global $\xi$-coordinates `xiCoordC`. The scaling $c_k$ does not appear on the left, since `piDs` depends only on the projection to $S$.
-- source:
--   Auxiliary to U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `uₖ` be finite-energy `J̃`-holomorphic planes in the symplectization of `S ⊂ ℝ⁴`, let `cₖ > 0`,
and suppose `cₖ • uₖ → w` in `C^∞_loc(U)`, with `w` a finite-energy curve on the open set `U`. For every
continuous curve `L` in a compact subset of `U`, the functions `t ↦ π ∂ₛ(uₖ)(L t)` converge locally
uniformly to `t ↦ π ∂ₛ(w)(L t)`. -/
theorem tendstoLocallyUniformly_piDs_comp (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hUo : IsOpen U)
    (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J U w) (u : ℕ → ℂ → V 1)
    (hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k)) (c : ℕ → ℝ) (hcpos : ∀ k, 0 < c k)
    (hconv : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • u k z) w U)
    (L : ℝ → ℂ) (hLc : Continuous L) (S : Set ℂ) (hSc : IsCompact S) (hSU : S ⊆ U)
    (hLS : ∀ t, L t ∈ S) :
    TendstoLocallyUniformly (fun k t => piDs H (u k) (L t)) (fun t => piDs H w (L t)) atTop := by
  sorry

end FiniteEnergyPlane
