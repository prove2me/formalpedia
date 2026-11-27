-- Prove2me | Theorems.Thm_DistTransform_Distortion_Supplement_theorem_2
-- name    : DistTransform.Distortion.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T13:08:55.836661+00:00
-- url     : https://prove2.me/theorems/5e7b7c55-f631-4be9-88bd-8ef150ecd304
-- title:
--   Theorem 2 — monotone constant-preserving additive transforms and Choquet families
-- statement:
--   Let M∞ be all bounded probability distributions on ℝ. Let T:M∞→M∞ be an arbitrary distributional transform. Let F⊕G denote comonotonic addition, δ_x the constant law, and H all increasing h:[0,1]→ℝ with h(0)=0 and h(1)=1. Write I_h for the Choquet integral in Eq. (7). Then
--
--   $$
--   \begin{gathered}
--   T\text{ is monotone, preserves every }\delta_x\text{ and is additive}\\
--   \Longleftrightarrow\quad\exists(h_p)_{0<p<1}\text{ pointwise increasing in }H:\quad
--   \forall F\in M_\infty,\quad (T(F))^{-1}(p)=I_{h_p}(F)\text{ for a.e. }p\in(0,1).
--   \end{gathered}
--   $$
--
--   For each F, this identity uniquely determines the output law T(F). A single family works for every bounded input, while the exceptional null set may depend on F. H has no continuity requirement, and the theorem does not require lower semicontinuity or shape commutation. This characterizes additive transforms more generally than the probability distortions in the mission goal.
--
--   Differences from the source:
--   - encoding: T:M∞→M∞ → a function on ProbabilityMeasure ℝ with MapsTo T Minf Minf; reason: only its bounded-law restriction is used, with exactly the stipulated domain and codomain
--   - encoding: F⊕G is the distribution with quantile F⁻¹+G⁻¹ → classical definite description by all interior quantiles; reason: this selects the uniquely specified source law and adds no existence premise
--   - encoding: h_p on [0,1] for p∈(0,1) → real functions constrained on exactly these intervals; reason: extensions outside the source intervals never enter the result
--   - encoding: T(F) is uniquely determined by Eq. (8) → every probability law G satisfying the same almost-everywhere identity equals T(F); reason: uniqueness concerns the output law, without imposing uniqueness of the family or a uniform exceptional null set
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 11, Theorem 2, Eqs. (7)–(8); conclusion of proof p. 12

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_Choquet

namespace DistTransform.Distortion.Supplement

open MeasureTheory

/-- Theorem 2, p. 11. One family works for all bounded laws, with a per-law
Lebesgue null set. Uniqueness concerns the output law, not the family. -/
theorem theorem_2 (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hT : Set.MapsTo T Minf Minf) :
    (IsMonotoneT Minf T ∧ PreservesConstants T ∧ IsAdditive T) ↔
      ∃ h : ℝ → ℝ → ℝ, IsOrderedFamily h ∧
        ∀ F ∈ Minf, Represents h F (T F) ∧
          ∀ G : ProbabilityMeasure ℝ, Represents h F G → G = T F := by sorry

end DistTransform.Distortion.Supplement
