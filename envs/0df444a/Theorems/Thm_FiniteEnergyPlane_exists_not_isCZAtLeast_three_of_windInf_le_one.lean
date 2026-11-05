-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_not_isCZAtLeast_three_of_windInf_le_one
-- name    : FiniteEnergyPlane.exists_not_isCZAtLeast_three_of_windInf_le_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T16:24:47.811585+00:00
-- url     : https://prove2.me/theorems/326b6990-341d-421d-90a2-2a57edf08059
-- title:
--   Punctured spheres with $\mathrm{wind}_\infty\le1$ at the positive puncture have a negative end of index below three
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $\Gamma\subset\mathbb{C}$ be finite and nonempty and $u$ a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$ with $\int_{\mathbb{C}\setminus\Gamma}u^*d\lambda>0$, such that $\infty$ is a positive puncture and every $z\in\Gamma$ a negative puncture, all nondegenerate in the sense of Hryniewicz, Definition 2.9, with nondegenerate asymptotic limits at the points of $\Gamma$. If $\mathrm{wind}_\infty(u,\infty)\le1$, then at some $z\in\Gamma$ the asymptotic limit $P_z$ satisfies $\mu_{CZ}(P_z)<3$.
--
--   **Formalization Note** The conclusion is `¬ Pz.IsCZAtLeast 3` for an orbit `Pz` with `IsNondegenerateEnd H u (cylEndAt z) Pz (-1)`, i.e. some transported orbit and linearized flow have `czIndexOfPath < 3`. The limit at $\infty$ need not be nondegenerate.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 4.15

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 4.15. Let `u` be a finite-energy `J̃`-holomorphic curve on
`ℂ \ Γ`, `Γ` finite and nonempty, in the symplectization of `S ⊂ ℝ⁴`, with positive `dλ`-energy,
a positive puncture at `∞` and negative punctures at the points of `Γ`, all nondegenerate in the
sense of Definition 2.9, and with nondegenerate asymptotic limits at the points of `Γ`. If
`wind_∞(u, ∞) ≤ 1`, then the asymptotic limit at some point of `Γ` has Conley–Zehnder index less
than `3`. -/
theorem exists_not_isCZAtLeast_three_of_windInf_le_one (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (hΓne : Γ.Nonempty) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u)
    (Pinf : ReebOrbit H) (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, Pz.IsNondegenerate ∧
      IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hpos : dlambdaEnergy H (↑Γ)ᶜ u ≠ 0) (k : ℤ) (hk : HasWindInfAt H u cylInf 1 k)
    (hk1 : k ≤ 1) :
    ∃ z ∈ Γ, ∃ Pz : ReebOrbit H, Pz.IsNondegenerate ∧
      IsNondegenerateEnd H u (cylEndAt z) Pz (-1) ∧ ¬ Pz.IsCZAtLeast 3 := by
  sorry

end FiniteEnergyPlane
