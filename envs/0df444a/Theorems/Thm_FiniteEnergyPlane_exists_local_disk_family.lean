-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_local_disk_family
-- name    : FiniteEnergyPlane.exists_local_disk_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:37:11.791441+00:00
-- url     : https://prove2.me/theorems/99e96097-92fd-5402-bd74-e57a1f9f2320
-- title:
--   One-parameter families of embedded disks with boundary on a surface
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $e$ embed the disk of radius $\rho>1$ into $S$ so that, on $B_\rho$, the characteristic field vanishes only at $z_0$, which is positive and nicely elliptic, and let $r<\rho$. Let $u$ be an embedded $\tilde J$-holomorphic disk with boundary loop in $e(B_r)$ of winding number $1$ around $e(z_0)$, and let $l\ge1$. Then there are $\varepsilon>0$ and
--   $$\Phi\in C^l\big((-\varepsilon,\varepsilon)\times D,\ \mathbb{R}^4\big),\qquad \Phi(0,\cdot)=u,$$
--   such that
--
--   1. every $\Phi(\tau,\cdot)$ is an embedded $\tilde J$-holomorphic disk with boundary loop in $e(B_r)$ of winding number $1$ around $e(z_0)$;
--   2. $\Phi$ is injective with injective derivative;
--   3. if $v_k$ are disks as in 1 converging to $u$ in $C^\infty(D)$, then for all large $k$ there is $\tau\in(-\varepsilon,\varepsilon)$ with $v_k(D)=\Phi(\tau,D)$.
--
--   Here $D$ is the closed unit disk. By 2 the images of different members are disjoint, and by 3 they are all the nearby disks up to reparametrization.
--
--   **Formalization Note** The map $\Phi$ is prescribed on $(-\varepsilon,\varepsilon)\times D$ only; derivatives are taken within this set. The radius $r<\rho$ ensures that $e$ is an embedding up to the boundary of the region containing the loops. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorems 17 and 18

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorems 17 and 18. Let `e` embed the disk of radius `ρ > 1` into `S` with exactly one
characteristic zero `z₀` there, positive and nicely elliptic, and let `u` be an embedded `J̃`-holomorphic disk
with boundary loop in `e({|z| < r})`, `r < ρ`, winding once around `e z₀`. For every `l ≥ 1` there are `ε > 0` and a `C^l` family
`Φ` on `(-ε, ε) × D` of such disks with `Φ(0, ·) = u`, which is injective with injective derivative.
Moreover, if such disks `v_k` converge to `u` in `C^∞` on the closed disk, then for all large `k` the image
of `v_k` is the image of some `Φ(τ, ·)`. -/
theorem exists_local_disk_family (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (z₀ : ℂ) (r : ℝ) (hr : r < ρ)
    (hz₀ : HasNicelyEllipticPoint e z₀ ρ) (u : ℂ → V 1)
    (hu : IsEmbeddedHoloDisk H J e z₀ (ball 0 r) u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ Φ : ℝ × ℂ → V 1,
      ContDiffOn ℝ l Φ (Set.Ioo (-ε) ε ×ˢ closedBall 0 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, Φ (0, z) = u z) ∧
      (∀ τ ∈ Set.Ioo (-ε) ε, IsEmbeddedHoloDisk H J e z₀ (ball 0 r) (fun z => Φ (τ, z))) ∧
      Set.InjOn Φ (Set.Ioo (-ε) ε ×ˢ closedBall 0 1) ∧
      (∀ p ∈ Set.Ioo (-ε) ε ×ˢ closedBall (0 : ℂ) 1,
        Function.Injective (fderivWithin ℝ Φ (Set.Ioo (-ε) ε ×ˢ closedBall 0 1) p)) ∧
      ∀ v : ℕ → ℂ → V 1, (∀ k, IsEmbeddedHoloDisk H J e z₀ (ball 0 r) (v k)) →
        TendstoCInftyLocWithin v u (closedBall 0 1) ∅ →
        ∀ᶠ k in atTop, ∃ τ ∈ Set.Ioo (-ε) ε,
          v k '' closedBall 0 1 = (fun z => Φ (τ, z)) '' closedBall 0 1 := by
  sorry

end FiniteEnergyPlane
