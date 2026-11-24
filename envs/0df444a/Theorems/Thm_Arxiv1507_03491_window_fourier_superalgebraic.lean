-- Prove2me | Theorems.Thm_Arxiv1507_03491_window_fourier_superalgebraic
-- name    : Arxiv1507_03491.window_fourier_superalgebraic
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:30:05.647564+00:00
-- url     : https://prove2.me/theorems/d0daf925-6cef-46bc-9ef9-706dd4e431ab
-- title:
--   Lemma 2.1: the Fourier transform of the window decays superalgebraically
-- statement:
--   Let $M_0>0$. The window $\tilde W_{M_0}$ of eq. (2.10) is integrable on $\mathbb R$ and its Fourier transform $\hat{\tilde W}_{M_0}(\lambda)=\int\tilde W_{M_0}(x)e^{-i\lambda x}dx$ decays superalgebraically: for every $n$ there are $C,R$ with
--
--   $$|\lambda|^n\,\big|\hat{\tilde W}_{M_0}(\lambda)\big|\le C\qquad(|\lambda|\ge R).$$
--
--   If moreover $M_0>4$, the same holds for the bump window $W_{M_0}$ of eq. (2.9).
--
--   The lemma supplies the decay of $\hat W$ that Theorem 2.2 uses.
--
--   **Formalization Note** The lemma names $W_{M_0}$, the symbol of the bump window (2.9), but cites eq. (2.10), the erf window. Both readings are included: the erf window as printed, and the bump window, which is the one Theorem 2.2 needs. Integrability is part of the conclusion so that the Fourier transform is a genuine Lebesgue integral.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c004; Section 2, Lemma 2.1 (window of eq. (2.10); also the window $W_{M_0}$ of eq. (2.9) used in Theorem 2.2), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem window_fourier_superalgebraic (M0 : ℝ) (hM0 : 0 < M0) :
    (Integrable (fun x : ℝ => (erfWindow M0 x : ℂ)) ∧
      SuperalgDecay (fourierT (fun x : ℝ => (erfWindow M0 x : ℂ)))) ∧
    (4 < M0 → Integrable (fun x : ℝ => (window M0 x : ℂ)) ∧
      SuperalgDecay (fourierT (fun x : ℝ => (window M0 x : ℂ)))) := by sorry

end Arxiv1507_03491
