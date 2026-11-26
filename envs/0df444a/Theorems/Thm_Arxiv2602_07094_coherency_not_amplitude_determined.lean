-- Prove2me | Theorems.Thm_Arxiv2602_07094_coherency_not_amplitude_determined
-- name    : Arxiv2602_07094.coherency_not_amplitude_determined
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:39:16.708286+00:00
-- url     : https://prove2.me/theorems/767bda80-ad95-5be9-b9dd-9e430ed505ba
-- title:
--   Section 4: the entries of the sample coherency matrix (7) are not functions of the channel amplitudes
-- statement:
--   Let $N\ge1$ and let $(a,b)$ be an index pair of a $3\times3$ matrix other than $(3,3)$ (the $\gamma\bar\gamma$ entry). For reciprocal Sinclair matrices $\mathbf S_1,\dots,\mathbf S_N$ with Pauli vectors $\mathbf k_i$, let $\hat{\mathbf T}=\frac1N\sum_i\mathbf k_i\mathbf k_i^H$. Then there is no function $F$ of the $N$ amplitude matrices $(|(S_i)_{jl}|)_{j,l}$, $i=1,\dots,N$, such that
--
--   $$\hat T_{ab}=F\big((|(S_1)_{jl}|),\dots,(|(S_N)_{jl}|)\big)$$
--
--   for all reciprocal $\mathbf S_1,\dots,\mathbf S_N$. So the diagonal entries $\hat T_{11},\hat T_{22}$ and all off-diagonal entries of the sample coherency matrix depend on the relative channel phases.
--
--   **Formalization Note** Indices run over $\{0,1,2\}$ in Lean, so the excluded entry is $(2,2)$. That entry equals $\frac2N\sum_i|(S_i)_{hv}|^2$ and is a function of the amplitudes; the statement does not claim otherwise.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), claim c024; Section 4, opening paragraph, PDF p. 10, with Section 3.1, eq. (7), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

open Matrix

namespace Arxiv2602_07094

theorem coherency_not_amplitude_determined (N : ℕ) (hN : 1 ≤ N) (a b : Fin 3)
    (hab : ¬ (a = 2 ∧ b = 2)) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℂ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) →
        sampleCoherency (fun i => pauliVector (S i)) a b = F (fun i => channelAmplitudes (S i)) := by sorry

end Arxiv2602_07094
