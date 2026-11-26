-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_spanningDisk_one_nicelyElliptic
-- name    : FiniteEnergyPlane.exists_spanningDisk_one_nicelyElliptic
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:12:33.349196+00:00
-- url     : https://prove2.me/theorems/de0e95b1-2fca-476e-a4b6-deb96ddfd8a1
-- title:
--   Spanning disks with a single tangency
-- statement:
--   Let $S=H_0^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $P=(x,T)$ a prime periodic orbit of $X_{H_0}$ on $S$ of self-linking number $-1$. If $x(\mathbb{R})$ has a spanning disk in $S$, then it has a spanning disk whose characteristic field has exactly one zero, positive and nicely elliptic.
--
--   That the zero is positive and nicely elliptic means that the linearization of the characteristic field has two positive real eigenvalues, possibly equal. No nondegeneracy and no index condition is assumed for $P$.
--
--   **Formalization Note** The zero is the only one on the open disk of radius $\rho'>1$ on which the new disk is embedded, and lies in the open unit disk (`HasNicelyEllipticPoint`). In the sources the new disk is smoothly isotopic to the given one, or $C^0$-close to it; this is not stated. Periodic orbits $P$ of $X_{H_0}$ are those of `HryniewiczCriterion_Basic`, in the coordinates `R4`; the level and the orbit are transported by the coordinate-preserving identification `ofR4` with `V 1`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, Theorem 3.1; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Theorem 3.1

import Definitions.Def_FiniteEnergyPlane_DiskFoliation
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999, tight sphere II), Theorem 3.1; Hryniewicz (2014), Theorem 3.1. Let `P` be a
prime periodic orbit of self-linking number `-1` whose image has a spanning disk. Then its image has a spanning disk
whose characteristic field has exactly one zero, positive and nicely elliptic. -/
theorem exists_spanningDisk_one_nicelyElliptic (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) (P : HryniewiczCriterion.PeriodicOrbit H₀)
    (hP : P.IsPrime) (hsl : HryniewiczCriterion.HasSelfLinkingNumber H₀ P (-1)) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ (e : ℂ → V 1) (ρ : ℝ), IsSpanningDisk H (Set.range fun τ => ofR4 (P.x τ)) e ρ →
    ∃ (e' : ℂ → V 1) (ρ' : ℝ) (z₀ : ℂ),
      IsSpanningDisk H (Set.range fun τ => ofR4 (P.x τ)) e' ρ' ∧ HasNicelyEllipticPoint e' z₀ ρ' := by
  sorry

end FiniteEnergyPlane
