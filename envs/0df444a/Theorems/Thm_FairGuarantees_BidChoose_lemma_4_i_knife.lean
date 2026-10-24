-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_lemma_4_i_knife
-- name    : FairGuarantees.BidChoose.lemma_4_i_knife
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:47.301628+00:00
-- url     : https://prove2.me/theorems/295a34d1-9b5b-49b5-861d-bbeaca2d6eb9
-- title:
--   Lemma 4 i), p. 19, κ part — the knife utility u^κ is continuous on the triangle
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ ($d\ge1$) be a manna, $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$ and $\kappa$ a moving knife. The knife utility
--   $$
--   u^\kappa(t^1,t^2)=u\big(K(t^2)\setminus K(t^1)\big)
--   $$
--   is continuous on the triangle $\mathcal T=\{(t^1,t^2):0\le t^1\le t^2\le1\}$.
--
--   Continuity of $u^\kappa$ is what the intermediate value argument for an equalising knife sequence (Lemma 4 ii)) needs.
--
--   **Formalization Note.** Only the $\kappa$ part of Lemma 4 i) is stated. The page also asserts that $u^\theta$ is continuous and that the min and max in (5) are attained; both claims fail for some $u\in\mathcal M^+([0,1])$ with $\theta$ Lebesgue measure and are not part of this item. Continuity is `ContinuousOn` on the triangle as a subset of $\mathbb R^2$.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 19, Lemma 4 i) (κ part); proof in the Appendix, pp. 24–25

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- Lemma 4 i), p. 19, the κ part: the knife utility `u^κ` is continuous on the triangle
`T = {(t¹, t²) | 0 ≤ t¹ ≤ t² ≤ 1}`. -/
theorem lemma_4_i_knife {d : ℕ} (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) :
    ContinuousOn (fun p : ℝ × ℝ => uKnife u K p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by sorry

end FairGuarantees.BidChoose
