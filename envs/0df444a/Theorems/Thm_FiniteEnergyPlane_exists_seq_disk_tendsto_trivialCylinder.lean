-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_seq_disk_tendsto_trivialCylinder
-- name    : FiniteEnergyPlane.exists_seq_disk_tendsto_trivialCylinder
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:39:13.164051+00:00
-- url     : https://prove2.me/theorems/39a1e5e7-7d39-59ee-a414-a35c458876cf
-- title:
--   Embedded disks converging to the trivial half-cylinder over the orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a prime periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Suppose $\int_{\mathring D}\max(\omega_0(\partial_se,\partial_te),0)<C$ and every periodic Reeb orbit of period at most $C$ is nondegenerate. Suppose that there is no embedded punctured $\tilde J$-holomorphic disk with boundary loop in $e(D)$ of winding number $1$ around $e(z_0)$, positive $d\lambda$-energy and a nonempty set of punctures, all negative and asymptotic to orbits of period at most $C$. If there is an embedded $\tilde J$-holomorphic disk with boundary loop in $e(\mathring D)$ of winding number $1$ around $e(z_0)$, disjoint from $\mathbb{R}\times x(\mathbb{R})$, then there is a sequence $(u_n)$ of such disks with
--   $$u_n\to F_P\quad\text{in }C^\infty_{loc}(D\setminus\{0\}),\qquad F_P(e^{2\pi(s+it)})=(Ts,\,x(Tt))\in\mathbb{R}\times S .$$
--
--   $D$ is the closed unit disk and $\mathring D$ the open one. The convergence is up to the boundary of $D$.
--
--   **Formalization Note** $F_P$ is `trivialCylinder P`, in the coordinates $y=e^{2a}x$. The hypothesis on punctured disks is the conclusion of `exists_xiClose_forall_not_puncturedDisk`, for loops in $e(D)$. Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Theorem 3.7; H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, Proposition 3.2 and Lemmas 3.3, 3.4 and 3.5

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), Theorem 3.7; Hofer–Wysocki–Zehnder (1999, tight 3-sphere II), Proposition 3.2 and Lemmas
3.3–3.5. Let `e` be a special spanning disk for the prime orbit `P`, of positive area less than `C`, and suppose
every periodic orbit of period at most `C` is nondegenerate. Suppose there is no embedded punctured
`J̃`-holomorphic disk with boundary on `e`, winding once around `e z₀`, with `∫ u*dλ > 0` and with a
nonempty set of punctures, all negative and asymptotic to orbits of period at most `C`. If there is an embedded
`J̃`-holomorphic disk with boundary in the interior of `e`, winding once around `e z₀` and disjoint from
`ℝ × x(ℝ)`, then there is a sequence of such disks that converges, in `C^∞_loc` on the closed disk minus `0`,
to the trivial cylinder over `P`. -/
theorem exists_seq_disk_tendsto_trivialCylinder (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (C : ℝ) (hC : diskArea e < ENNReal.ofReal C)
    (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate)
    (hJe : ∀ (Γ : Finset ℂ) (u : ℂ → V 1), Γ.Nonempty →
      IsDiskCurve H J e z₀ (closedBall 0 1) Γ u → IsEmbeddedOnDisk Γ u →
      0 < dlambdaEnergy H (ball 0 1 \ Γ) u →
      ¬ ∀ z ∈ Γ, ∃ Q : ReebOrbit H, Q.T ≤ C ∧ IsNondegenerateEnd H u (cylEndAt z) Q (-1))
    (u₀ : ℂ → V 1) (hu₀ : IsEmbeddedHoloDisk H J e z₀ (ball 0 1) u₀)
    (hdis : ∀ z ∈ closedBall (0 : ℂ) 1, proj H (u₀ z) ∉ Set.range P.x) :
    ∃ u : ℕ → ℂ → V 1, (∀ n, IsEmbeddedHoloDisk H J e z₀ (ball 0 1) (u n)) ∧
      (∀ n, ∀ z ∈ closedBall (0 : ℂ) 1, proj H (u n z) ∉ Set.range P.x) ∧
      TendstoCInftyLocWithin u (trivialCylinder P) (closedBall 0 1) {0} := by
  sorry

end FiniteEnergyPlane
