-- Prove2me | Theorems.Thm_Arxiv2602_07094_entropy_not_amplitude_determined
-- name    : Arxiv2602_07094.entropy_not_amplitude_determined
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:39:48.861518+00:00
-- url     : https://prove2.me/theorems/ff034dfd-7fcc-4f7c-9ef5-8536721ce665
-- title:
--   Section 4: the entropy H is not a function of the channel amplitudes (N ≥ 2 samples)
-- statement:
--   Let $N\ge2$. For reciprocal Sinclair matrices $\mathbf S_1,\dots,\mathbf S_N$, not all zero, let $H$ be the entropy of their sample coherency matrix $\hat{\mathbf T}=\frac1N\sum_i\mathbf k_i\mathbf k_i^H$, that is $H=-\sum_ip_i\log_3p_i$ with $p_i$ the normalised eigenvalues of $\hat{\mathbf T}$. Then there is no function $F$ of the amplitude matrices of $\mathbf S_1,\dots,\mathbf S_N$ such that
--
--   $$H(\hat{\mathbf T})=F\big((|(S_1)_{jl}|),\dots,(|(S_N)_{jl}|)\big)$$
--
--   for all such families. Two families with the same channel amplitudes can therefore have different entropies.
--
--   **Formalization Note** The paper states the claim for a boxcar of $N$ samples without fixing $N$. For $N=1$ the claim is false: $\hat{\mathbf T}=\mathbf k\mathbf k^H$ has rank one and $H=0$ for every nonzero $\mathbf S$. The statement therefore assumes $N\ge2$. The entropy is the Cloude–Pottier form $-\sum p_i\log_3p_i$; the paper's printed form $\sum p_i\log p_i$ is the same function multiplied by the nonzero constant $-\ln3$, so the statement is the same for either.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), claim c024; Section 4, opening paragraph, PDF p. 10, with Section 3.1, eq. (7) and the definition of H, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

open Matrix

namespace Arxiv2602_07094

theorem entropy_not_amplitude_determined (N : ℕ) (hN : 2 ≤ N) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
        entropyH (sampleCoherency (fun i => pauliVector (S i))) =
          F (fun i => channelAmplitudes (S i)) := by sorry

end Arxiv2602_07094
