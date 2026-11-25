-- Prove2me | Theorems.Thm_Arxiv2105_07250_source_kernel_expansion
-- name    : Arxiv2105_07250.source_kernel_expansion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:31:22.941714+00:00
-- url     : https://prove2.me/theorems/3db88568-604b-5f9d-b020-c14db8a0cb2d
-- title:
--   Eq. (A30): the stacking kernel of a random-phase broadband source
-- statement:
--   Let $\tilde\Omega$ be a finite set of distinct frequencies $w_i$ with real coefficients $a_i$, and let $(\theta_i)$ be real random phases with an arbitrary joint law on a probability space. For the source signature $F(t';\theta)=\sum_i a_i\cos(w_it'+\theta_i)$ (A27) and all $t',t''$,
--
--   $$\begin{aligned}\langle F(t')F(t'')\rangle=&\sum_i a_i^2\big(\cos(w_it')\cos(w_it'')\langle\cos^2\theta_i\rangle-\sin(w_i(t'+t''))\langle\cos\theta_i\sin\theta_i\rangle+\sin(w_it')\sin(w_it'')\langle\sin^2\theta_i\rangle\big)\\&+\sum_i\sum_{j\ne i}a_ia_j\big(\cos(w_it')\cos(w_jt'')\langle\cos\theta_i\cos\theta_j\rangle-\cos(w_it')\sin(w_jt'')\langle\cos\theta_i\sin\theta_j\rangle\\&\qquad-\sin(w_it')\cos(w_jt'')\langle\sin\theta_i\cos\theta_j\rangle+\sin(w_it')\sin(w_jt'')\langle\sin\theta_i\sin\theta_j\rangle\big).\end{aligned}$$
--
--   **Formalization Note** $F$ is real, so the paper's $\langle F^*(t')F^*(t'')\rangle$ in (A30) equals $\langle F(t')F(t'')\rangle$. The phases are assumed measurable. The stacked retrieval (A29), in which this kernel appears, is not included: its double integral over $t',t''$ is not absolutely convergent (see REPORT.md).
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c027; Appendix B, eq. (A30), PDF p. 38

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem source_kernel_expansion {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (w a : ι → ℝ) (hw : Function.Injective w)
    (θ : ι → Ω → ℝ) (hθ : ∀ i, Measurable (θ i)) (t' t'' : ℝ) :
    ∫ r, sourceSignature w a (fun i => θ i r) t' * sourceSignature w a (fun i => θ i r) t'' ∂P =
      (∑ i, a i ^ 2 *
          (Real.cos (w i * t') * Real.cos (w i * t'') * ∫ r, Real.cos (θ i r) ^ 2 ∂P
            - Real.sin (w i * (t' + t'')) * ∫ r, Real.cos (θ i r) * Real.sin (θ i r) ∂P
            + Real.sin (w i * t') * Real.sin (w i * t'') * ∫ r, Real.sin (θ i r) ^ 2 ∂P)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, a i * a j *
          (Real.cos (w i * t') * Real.cos (w j * t'') * ∫ r, Real.cos (θ i r) * Real.cos (θ j r) ∂P
            - Real.cos (w i * t') * Real.sin (w j * t'') *
                ∫ r, Real.cos (θ i r) * Real.sin (θ j r) ∂P
            - Real.sin (w i * t') * Real.cos (w j * t'') *
                ∫ r, Real.sin (θ i r) * Real.cos (θ j r) ∂P
            + Real.sin (w i * t') * Real.sin (w j * t'') *
                ∫ r, Real.sin (θ i r) * Real.sin (θ j r) ∂P) := by sorry

end Arxiv2105_07250
