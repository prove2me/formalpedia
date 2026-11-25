-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_amplitudes_asymptotically_independent
-- name    : Arxivcond_mat_0004049.amplitudes_asymptotically_independent
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:13:40.343784+00:00
-- url     : https://prove2.me/theorems/b5d94b8d-0614-4675-b1a5-bcf886893688
-- title:
--   Asymptotic independence of A_0, A_1 and of C_0, C_1
-- statement:
--   Let $\gamma>0$. In the localized regime the quantities $A_0$ and $A_1$ ($n\ne m$), and likewise $C_0$ and $C_1$ ($n=m$), become mutually independent in the large-$N$ limit. On their natural scales $A_0,C_0\sim N^{-1/2}$ and $A_1,C_1\sim\gamma N$: the joint law of $(N^{1/2}A_0,\,A_1/(\gamma N))$ converges as $N\to\infty$ to a product $\alpha\otimes\beta$ of two probability measures on $\mathbb{C}$, neither a point mass. The same holds for $(N^{1/2}C_0,\,C_1/(\gamma N))$.
--
--   **Formalization Note** "Become mutually independent in the large-$N$ limit" is stated as convergence of the rescaled pair to a product law. The limits are required not to be point masses, so that the rescaling does not make independence trivial.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c020; qualitative argument after Fig. 2, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem amplitudes_asymptotically_independent (γ : ℝ) (hγ : 0 < γ) :
    (∃ α β : Measure ℂ, IsProbabilityMeasure α ∧ IsProbabilityMeasure β ∧
      (∀ z : ℂ, α ≠ Measure.dirac z ∧ β ≠ Measure.dirac z) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => ((Real.sqrt N : ℂ) * ampA 0 ω, ampA 1 ω / ((γ * N : ℝ) : ℂ))) (α.prod β)) ∧
    (∃ α β : Measure ℂ, IsProbabilityMeasure α ∧ IsProbabilityMeasure β ∧
      (∀ z : ℂ, α ≠ Measure.dirac z ∧ β ≠ Measure.dirac z) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => ((Real.sqrt N : ℂ) * ampC 0 ω, ampC 1 ω / ((γ * N : ℝ) : ℂ))) (α.prod β)) := by sorry

end Arxivcond_mat_0004049
