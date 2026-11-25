-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_xiClose_forall_not_puncturedDisk
-- name    : FiniteEnergyPlane.exists_xiClose_forall_not_puncturedDisk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:37:59.425442+00:00
-- url     : https://prove2.me/theorems/4365fa7b-622c-50d5-bb8d-7da56071ac66
-- title:
--   For a dense set of $J$ there are no embedded punctured disks with negative punctures of index at least 3
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$. Let $e$ embed the disk of radius $\rho>1$ into $S$ so that, on $B_\rho$, the characteristic field vanishes only at $z_0$, which is positive and nicely elliptic. Suppose every periodic Reeb orbit of period at most $C$ is nondegenerate with $\mu_{CZ}\ge3$. Then for every compatible $J_0$, $k\ge0$ and $\varepsilon>0$ there is a compatible $J$ with
--   $$\|J-J_0\|_{C^k(S)}\le\varepsilon$$
--   for which there is no embedded punctured $\tilde J$-holomorphic disk $u$ such that
--
--   1. its boundary loop lies in $e(B_\rho)$ and has winding number $1$ around $e(z_0)$;
--   2. $\int u^*d\lambda>0$;
--   3. its set of punctures is nonempty, and every puncture is negative and asymptotic to a periodic Reeb orbit of period at most $C$.
--
--   One $J$ serves all sets of punctures and all asymptotic limits of period at most $C$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count. $\mu_{CZ}\ge3$ is `IsCZAtLeast 3`, measured in the global frame of $\xi$, which extends over every capping disk. The condition $\pi\circ Tu\ne0$ somewhere, of the source, is $\int u^*d\lambda>0$. In the source the characteristics of the disk moreover all emerge from the singular point; this is not assumed here. The homotopy class of the disks in the source is determined by the winding number on $S\cong S^3$ and is not restated (see `FiniteEnergyPlane_SpanningDisk`). The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory, in Topics in Nonlinear Analysis, Birkhäuser 1999, 381–475, Theorem 1.15; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Theorem 3.6

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999), *Properties III*, Theorem 1.15; Hryniewicz (2014), Theorem 3.6. Let `e` embed
the disk of radius `ρ > 1` into `S` with exactly one characteristic zero `z₀` there, positive and nicely elliptic.
Suppose every periodic orbit of period at most `C` is nondegenerate of Conley–Zehnder index at least `3`.
Arbitrarily close in `C^k`, for every `k`, to every compatible `J₀` there is a compatible `J` for which there
is no embedded punctured `J̃`-holomorphic disk with boundary on `e`, winding once around `e z₀`, with
`∫ u*dλ > 0` and with a nonempty set of punctures, all negative and asymptotic to orbits of period
at most `C`. -/
theorem exists_xiClose_forall_not_puncturedDisk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (z₀ : ℂ)
    (hz₀ : HasNicelyEllipticPoint e z₀ ρ) (C : ℝ)
    (hQ : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (J₀ : V 1 → V 1 →L[ℝ] V 1) (hJ₀ : IsCompatibleXiStructure H J₀) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J ∧ IsXiClose H k ε J J₀ ∧
      ∀ (Γ : Finset ℂ) (u : ℂ → V 1), Γ.Nonempty → IsDiskCurve H J e z₀ (ball 0 ρ) Γ u →
        IsEmbeddedOnDisk Γ u → 0 < dlambdaEnergy H (ball 0 1 \ Γ) u →
        ¬ ∀ z ∈ Γ, ∃ Q : ReebOrbit H, Q.T ≤ C ∧ IsNondegenerateEnd H u (cylEndAt z) Q (-1) := by
  sorry

end FiniteEnergyPlane
