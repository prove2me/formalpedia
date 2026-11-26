-- Prove2me | Theorems.Thm_Arxiv2602_07094_alpha_angle_not_amplitude_determined
-- name    : Arxiv2602_07094.alpha_angle_not_amplitude_determined
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:40:37.860416+00:00
-- url     : https://prove2.me/theorems/4b42aa25-3550-4eb4-baba-d105b39c6a61
-- title:
--   Section 4: the mean alpha angle is not a function of the channel amplitudes
-- statement:
--   Let $N\ge1$. For reciprocal Sinclair matrices $\mathbf S_1,\dots,\mathbf S_N$, not all zero, whose sample coherency matrix $\hat{\mathbf T}$ has pairwise distinct nonzero eigenvalues, let $\bar\alpha(\hat{\mathbf T})=\sum_ip_i\arccos|e_{i1}|$ be the mean alpha angle. Then there is no function $F$ of the amplitude matrices of $\mathbf S_1,\dots,\mathbf S_N$ such that
--
--   $$\bar\alpha(\hat{\mathbf T})=F\big((|(S_1)_{jl}|),\dots,(|(S_N)_{jl}|)\big)$$
--
--   for all such families. Two families with the same channel amplitudes can therefore have different alpha angles.
--
--   **Formalization Note** The paper defines $\alpha_i$ through "the $i$-th eigenvector", which is ambiguous when a positive eigenvalue is repeated. The statement ranges only over families whose positive eigenvalues are distinct, where $\bar\alpha$ is well defined. Restricting the domain makes the non-existence of $F$ a stronger statement, not a weaker one.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), claim c024; Section 4, opening paragraph, PDF p. 10, with Section 3.1, eq. (7) and the definition of the angle alpha, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

open Matrix

namespace Arxiv2602_07094

theorem alpha_angle_not_amplitude_determined (N : ℕ) (hN : 1 ≤ N) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
        HasSimplePositiveSpectrum (sampleCoherency (fun i => pauliVector (S i))) →
        alphaAngle (sampleCoherency (fun i => pauliVector (S i))) =
          F (fun i => channelAmplitudes (S i)) := by sorry

end Arxiv2602_07094
