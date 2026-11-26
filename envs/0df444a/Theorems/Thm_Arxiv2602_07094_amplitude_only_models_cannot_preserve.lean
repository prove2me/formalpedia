-- Prove2me | Theorems.Thm_Arxiv2602_07094_amplitude_only_models_cannot_preserve
-- name    : Arxiv2602_07094.amplitude_only_models_cannot_preserve
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:41:26.610866+00:00
-- url     : https://prove2.me/theorems/c2fa7e93-c24c-43d1-b962-23221040db4a
-- title:
--   Section 4: amplitude-only models cannot preserve the Pauli and H-alpha quantities
-- statement:
--   An amplitude-only model sees, and outputs, only the channel amplitudes $|S_{ij}|$ of each pixel's Sinclair matrix. Its output can preserve a polarimetric quantity on all data only if that quantity is a function of the amplitudes. None of the following is:
--
--   1. the Pauli modulus $|\alpha(\mathbf S)|$ of a reciprocal Sinclair matrix;
--   2. the Pauli modulus $|\beta(\mathbf S)|$;
--   3. for every $N\ge1$, every entry $\hat T_{ab}$ of the sample coherency matrix $\hat{\mathbf T}=\frac1N\sum_{i=1}^N\mathbf k_i\mathbf k_i^H$ except the $\gamma\bar\gamma$ entry $(3,3)$;
--   4. for every $N\ge2$, the entropy $H(\hat{\mathbf T})$, on families that are not all zero;
--   5. for every $N\ge1$, the mean alpha angle $\bar\alpha(\hat{\mathbf T})$, on families that are not all zero and whose coherency matrix has distinct positive eigenvalues.
--
--   Here "not a function of the amplitudes" means that there is no map $F$ with $Q(\mathbf S_1,\dots,\mathbf S_N)=F\big((|(S_1)_{jl}|),\dots,(|(S_N)_{jl}|)\big)$ on the stated domain. This is the mathematical content of the paper's statement that amplitude-only models are "theoretically incapable" of preserving the Pauli and $H$-$\alpha$ properties, because these rely on the relative phase between polarisation channels.
--
--   **Formalization Note** The Cameron decomposition and the $H$-$\alpha$ zone of Figure 1 are not included: the paper describes Cameron's decomposition only in words and gives the zone boundaries only as a figure. The case $N=1$ is excluded for the entropy, where the claim fails. Indices are $0,1,2$ in Lean, so the excluded coherency entry is $(2,2)$.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), claim c024; Section 4, opening paragraph, PDF p. 10, with Section 3.1, eqs. (4) and (7) and the definitions of H and alpha, PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

open Matrix

namespace Arxiv2602_07094

theorem amplitude_only_models_cannot_preserve :
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliAlpha S‖ = F (channelAmplitudes S)) ∧
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliBeta S‖ = F (channelAmplitudes S)) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ a b : Fin 3, ¬ (a = 2 ∧ b = 2) →
      ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℂ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) →
          sampleCoherency (fun i => pauliVector (S i)) a b =
            F (fun i => channelAmplitudes (S i))) ∧
    (∀ N : ℕ, 2 ≤ N →
      ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
          entropyH (sampleCoherency (fun i => pauliVector (S i))) =
            F (fun i => channelAmplitudes (S i))) ∧
    (∀ N : ℕ, 1 ≤ N →
      ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
          HasSimplePositiveSpectrum (sampleCoherency (fun i => pauliVector (S i))) →
          alphaAngle (sampleCoherency (fun i => pauliVector (S i))) =
            F (fun i => channelAmplitudes (S i))) := by sorry

end Arxiv2602_07094
