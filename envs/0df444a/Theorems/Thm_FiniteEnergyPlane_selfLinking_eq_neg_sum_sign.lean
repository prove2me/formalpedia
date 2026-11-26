-- Prove2me | Theorems.Thm_FiniteEnergyPlane_selfLinking_eq_neg_sum_sign
-- name    : FiniteEnergyPlane.selfLinking_eq_neg_sum_sign
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:08:19.144213+00:00
-- url     : https://prove2.me/theorems/e611bd22-8ae0-4132-b81d-04b4fa5ce2bb
-- title:
--   The self-linking number as a signed count of tangencies
-- statement:
--   Let $S=H_0^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $P=(x,T)$ a prime periodic orbit of $X_{H_0}$ on $S$ with self-linking number $n$. Let $e$ be a spanning disk of $x(\mathbb{R})$ whose characteristic field $V$ has finitely many zeros in the closed unit disk, forming a set $Z$, all nondegenerate. Then
--   $$n=-\sum_{z\in Z}\operatorname{sign}\big(\mathrm{tr}\,DV(z)\big)\cdot\operatorname{sign}\big(\det DV(z)\big).$$
--
--   The zeros of $V$ are the points at which the disk is tangent to $\xi$, and the two signs at $z$ are the sign and the index of the tangency.
--
--   **Formalization Note** The self-linking number is `HasSelfLinkingNumber`, defined with the global frame of $\xi$, with the orientation for which a Hopf fibre of the round sphere has self-linking number $-1$. Periodic orbits $P$ of $X_{H_0}$ are those of `HryniewiczCriterion_Basic`, in the coordinates `R4`; the level and the orbit are transported by the coordinate-preserving identification `ofR4` with `V 1`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, formula (3.2); U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, formula (34)

import Definitions.Def_FiniteEnergyPlane_DiskFoliation
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999, tight sphere II), (3.2). Let `P` be a prime periodic orbit with self-linking number
`n`, and let `e` be a spanning disk of its image whose zeros in the closed unit disk are nondegenerate. Then
`n` is minus the sum over the zeros of the sign of the zero times its index. -/
theorem selfLinking_eq_neg_sum_sign (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) (P : HryniewiczCriterion.PeriodicOrbit H₀)
    (hP : P.IsPrime) (n : ℤ) (hsl : HryniewiczCriterion.HasSelfLinkingNumber H₀ P n) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ (e : ℂ → V 1) (ρ : ℝ), IsSpanningDisk H (Set.range fun τ => ofR4 (P.x τ)) e ρ →
    ∀ Z : Finset ℂ, (Z : Set ℂ) ⊆ closedBall 0 1 →
    (∀ z ∈ closedBall (0 : ℂ) 1, charField e z = 0 ↔ z ∈ Z) → (∀ z ∈ Z, charDet e z ≠ 0) →
    n = -∑ z ∈ Z, ((SignType.sign (charTrace e z) : SignType) : ℤ) *
      ((SignType.sign (charDet e z) : SignType) : ℤ) := by
  sorry

end FiniteEnergyPlane
