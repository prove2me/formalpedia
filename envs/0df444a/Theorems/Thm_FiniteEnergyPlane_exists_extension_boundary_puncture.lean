-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_extension_boundary_puncture
-- name    : FiniteEnergyPlane.exists_extension_boundary_puncture
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:35:22.236667+00:00
-- url     : https://prove2.me/theorems/350f20f2-6c52-5c29-b0f9-6a51697a8dbb
-- title:
--   Removal of a boundary puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $e$ embed the disk of radius $\rho>1$ into $S$, and let $K\subset B_\rho$ be a compact set of parameters on which the characteristic field of $e$ has no zero. $D$ is the closed unit disk and $\mathring D$ the open one. Let $u:D\setminus\{1\}\to\mathbb{R}^4\setminus\{0\}$ be smooth, $\tilde J$-holomorphic on $\mathring D$, with
--   $$E(u)<\infty,\qquad u(z)\in e(K)\ \text{ for }|z|=1,\ z\ne1 .$$
--   Then $u$ extends to a smooth map on $D$.
--
--   The theorem concerns the boundary point $1$; every other boundary point is moved to it by an automorphism of the disk.
--
--   **Formalization Note** The conclusion is the existence of $v$, smooth on $D$ (`ContDiffOn` on the closed ball), that agrees with $u$ on $D\setminus\{1\}$. The source has a half-plane; the disk minus a boundary point is the same domain. $E(u)$ is Hofer's energy on the open disk.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 32

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorem 32. Let `e` embed a disk into `S` and let `K` be a compact set of parameters on
which the characteristic field of `e` has no zero. Let `u` be smooth on the closed unit disk minus the
boundary point `1`, avoiding `0`, `J̃`-holomorphic with finite Hofer energy in the interior, with
`u(∂D \ {1}) ⊂ e(K)`. Then `u` extends to a smooth map on the closed unit disk. -/
theorem exists_extension_boundary_puncture (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ)
    (K : Set ℂ) (hK : IsCompact K) (hKρ : K ⊆ ball 0 ρ) (hK₀ : ∀ z ∈ K, charField e z ≠ 0)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ {1}))
    (hu₀ : ∀ z ∈ closedBall (0 : ℂ) 1 \ {1}, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1) u)
    (hE : energy H (ball 0 1) u < ⊤) (hb : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ 1 → u z ∈ e '' K) :
    ∃ v : ℂ → V 1, ContDiffOn ℝ ∞ v (closedBall 0 1) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ 1 → v z = u z := by
  sorry

end FiniteEnergyPlane
