-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_notMem_range_or_forall_mem_of_tendsto
-- name    : FiniteEnergyPlane.proj_notMem_range_or_forall_mem_of_tendsto
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T22:25:25.923582+00:00
-- url     : https://prove2.me/theorems/b6ef7cf3-986e-49ca-a2b6-6a4518b973fd
-- title:
--   Limits of curves missing a trivial cylinder miss it or lie in it
-- statement:
--   Let $S = H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with compatible $J$, and let $P = (x,T)$ be a periodic Reeb orbit. Let $U\subseteq\mathbb{C}$ be open and preconnected, let $u$ be a finite-energy $\tilde J$-holomorphic curve on $U$ with injective derivative at every point of $U$, and let $u_n$ be finite-energy $\tilde J$-holomorphic curves on $U$ converging to $u$ in $C^\infty_{\mathrm{loc}}(U)$, none of which meets the trivial cylinder $\mathbb{R}\times x(\mathbb{R})$ (i.e. $\mathrm{proj}\,u_n(z)\notin x(\mathbb{R})$ for all $z\in U$). Then either $u$ does not meet $\mathbb{R}\times x(\mathbb{R})$ on $U$, or $u(U)\subseteq\mathbb{R}\times x(\mathbb{R})$.
--
--   Role: the interior part of the statement that limits of pseudoholomorphic disks disjoint from $\mathbb{R}\times x(\mathbb{R})$ stay disjoint from it.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II (1995), Theorem 4.4 (interior part); D. McDuff, J. Differential Geom. 34 (1991)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Limits of curves missing a trivial cylinder. Let `P = (x, T)` be a periodic Reeb orbit and `U ⊆ ℂ` open and
preconnected. Let `u` be a finite-energy `J̃`-holomorphic immersion on `U`, and let finite-energy `J̃`-holomorphic
curves `u_n` on `U`, none of which meets `ℝ × x(ℝ)` (that is, `proj ∘ u_n` avoids `x(ℝ)` on `U`), converge to `u`
in `C^∞_loc(U)`. Then either `u` does not meet `ℝ × x(ℝ)` on `U`, or `u(U) ⊆ ℝ × x(ℝ)`. -/
theorem proj_notMem_range_or_forall_mem_of_tendsto (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U) (u : ℂ → V 1) (un : ℕ → ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hun : ∀ n, IsFiniteEnergyCurve H J U (un n))
    (hconv : JHolomorphic.TendstoCInftyLocOn un u U)
    (hdis : ∀ n, ∀ z ∈ U, proj H (un n z) ∉ Set.range P.x) :
    (∀ z ∈ U, proj H (u z) ∉ Set.range P.x) ∨ ∀ z ∈ U, proj H (u z) ∈ Set.range P.x := by
  sorry

end FiniteEnergyPlane
