-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_puncturedDisk
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_puncturedDisk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:38:48.905897+00:00
-- url     : https://prove2.me/theorems/4dd94c16-4698-41c3-89d3-34e9a9ad1e4c
-- title:
--   Subsequential limits of embedded disks are punctured disks
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a prime periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Suppose $\int_{\mathring D}\max(\omega_0(\partial_se,\partial_te),0)<C$ and every periodic Reeb orbit of period at most $C$ is nondegenerate. Let $K\subset D\setminus\{z_0\}$ be compact and $q_1,q_2,q_3$ distinct points of the unit circle. Let $u_n$ be embedded $\tilde J$-holomorphic disks whose boundary loops $t\mapsto e(c_n(t))$ lie in $e(K)$, have winding number $1$ around $e(z_0)$, and have $c_n(0),c_n(\tfrac14),c_n(\tfrac12)$ on the characteristic leaves through $q_1,q_2,q_3$. Then, for a subsequence, there are a finite $\Gamma\subset\mathring D$ and a punctured $\tilde J$-holomorphic disk $v$ with punctures $\Gamma$ such that
--   $$u_{\varphi(n)}\to v\quad\text{in }C^\infty_{loc}(D\setminus\Gamma),$$
--   up to the boundary of $D$, and:
--
--   1. the boundary loop of $v$ lies in $e(K)$ and has winding number $1$ around $e(z_0)$;
--   2. every puncture of $v$ is negative and asymptotic to a periodic Reeb orbit of period at most $C$;
--   3. $\int v^*d\lambda=0$, or $v$ is an embedding of $D\setminus\Gamma$.
--
--   $D$ is the closed unit disk and $\mathring D$ the open one. The set $\Gamma$ may be empty, and $K$ may meet the unit circle, so boundary loops of the limit may touch $x(\mathbb{R})$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, formulas (3.10)–(3.15) and Lemma 3.3; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, § 3.2

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999, tight 3-sphere II), (3.10)–(3.15) and Lemma 3.3; Hryniewicz (2014), § 3.2. Let `e` be a special spanning disk for the prime orbit `P`, of positive area less than `C`, and
suppose every periodic orbit of period at most `C` is nondegenerate. Let `u_n` be embedded `J̃`-holomorphic
disks whose boundary loops lie in `e(K)` for a fixed compact `K` in the closed unit disk, `z₀ ∉ K`, wind once around
`e z₀`, and meet the leaves through three fixed distinct points of the unit circle at `1, i, -1`. Then a
subsequence converges in `C^∞_loc` on the closed disk minus a finite set `Γ` of interior points to a punctured
`J̃`-holomorphic disk `v` with boundary on `e`, whose punctures are negative and asymptotic to orbits of period
at most `C`. Either `∫ v*dλ = 0`, or `v` is an embedding. -/
theorem exists_subseq_tendsto_puncturedDisk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (C : ℝ) (hC : diskArea e < ENNReal.ofReal C)
    (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate)
    (K : Set ℂ) (hK : IsCompact K) (hK₁ : K ⊆ closedBall 0 1) (hK₀ : z₀ ∉ K)
    (q₁ q₂ q₃ : ℂ) (hq₁ : q₁ ∈ sphere (0 : ℂ) 1) (hq₂ : q₂ ∈ sphere (0 : ℂ) 1)
    (hq₃ : q₃ ∈ sphere (0 : ℂ) 1) (h₁₂ : q₁ ≠ q₂) (h₂₃ : q₂ ≠ q₃) (h₁₃ : q₁ ≠ q₃)
    (u : ℕ → ℂ → V 1) (c : ℕ → ℝ → ℂ) (hu : ∀ n, IsEmbeddedHoloDisk H J e z₀ K (u n))
    (hc : ∀ n, HasDiskBoundary e z₀ K (u n) (c n))
    (hl : ∀ n, SameLeaf e (c n 0) q₁ ∧ SameLeaf e (c n (1 / 4)) q₂ ∧ SameLeaf e (c n (1 / 2)) q₃) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (Γ : Finset ℂ) (v : ℂ → V 1),
      IsDiskCurve H J e z₀ K Γ v ∧
      TendstoCInftyLocWithin (fun n => u (φ n)) v (closedBall 0 1) Γ ∧
      (∀ z ∈ Γ, ∃ Q : ReebOrbit H, Q.T ≤ C ∧ IsNondegenerateEnd H v (cylEndAt z) Q (-1)) ∧
      (dlambdaEnergy H (ball 0 1 \ Γ) v = 0 ∨ IsEmbeddedOnDisk Γ v) := by
  sorry

end FiniteEnergyPlane
