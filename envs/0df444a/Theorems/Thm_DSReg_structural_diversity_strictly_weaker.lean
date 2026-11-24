-- Prove2me | Theorems.Thm_DSReg_structural_diversity_strictly_weaker
-- name    : DSReg.structural_diversity_strictly_weaker
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:30:08.495536+00:00
-- url     : https://prove2.me/theorems/61bb57ac-2375-4044-9f07-4c96149b54d3
-- title:
--   Proposition 1: Structural Diversity is strictly weaker
-- statement:
--   Let $\mathcal S_1,\dots,\mathcal S_d\subseteq[p]$ be footprints. Each of the following conditions implies Structural Diversity ($\mathcal S_i\ne\mathcal S_j$ for $i\ne j$):
--
--   1. Structural Sparsity, intersection form: every $k\in[d]$ has a nonempty $\mathcal C_k\subseteq[p]$ with $\bigcap_{r\in\mathcal C_k}\{i:r\in\mathcal S_i\}=\{k\}$;
--   2. Structural Sparsity, overlap-rank form: $\big|\bigcup_{j\in\mathcal C}\mathcal S_j\big|-\operatorname{rank}(M^{\mathcal C})>|\mathcal S_k|$ for every $\mathcal C\subseteq[d]$ with $|\mathcal C|\ge2$ and every $k\in\mathcal C$;
--   3. Non-Inclusion: $\mathcal S_i\not\subseteq\mathcal S_j$ for all $i\ne j$, which is implied by both forms of Structural Sparsity;
--   4. Structural Variability: $|\mathcal S_i\triangle\mathcal S_j|\ge2$ for all $i\ne j$.
--
--   None of the converse implications holds: for each of the four conditions there are $d,p$ and footprints satisfying Structural Diversity but not that condition.
--
--   **Formalization Note** The ranks are over $\mathbb{R}$, and the difference in condition 2 is taken in the integers. The clause "a common weakening of both forms above" in condition 3 appears as the two implications from the Structural Sparsity forms to Non-Inclusion.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Section 3.2, Proposition 1, p. 6; proof in Appendix A.3, pp. 20-21

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem structural_diversity_strictly_weaker {d p : ℕ} (S : Fin d → Set (Fin p)) :
    (SSIntersection S → StructuralDiversity S) ∧
    (SSOverlapRank S → StructuralDiversity S) ∧
    (NonInclusion S → StructuralDiversity S) ∧
    (StructuralVariability S → StructuralDiversity S) ∧
    (SSIntersection S → NonInclusion S) ∧
    (SSOverlapRank S → NonInclusion S) ∧
    (∃ (d' p' : ℕ) (S' : Fin d' → Set (Fin p')), StructuralDiversity S' ∧ ¬ SSIntersection S') ∧
    (∃ (d' p' : ℕ) (S' : Fin d' → Set (Fin p')), StructuralDiversity S' ∧ ¬ SSOverlapRank S') ∧
    (∃ (d' p' : ℕ) (S' : Fin d' → Set (Fin p')), StructuralDiversity S' ∧ ¬ NonInclusion S') ∧
    (∃ (d' p' : ℕ) (S' : Fin d' → Set (Fin p')),
      StructuralDiversity S' ∧ ¬ StructuralVariability S') := by sorry

end DSReg
