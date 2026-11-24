-- Prove2me | Theorems.Thm_CompressedSensingRadar_random_subdictionary_conditioning
-- name    : CompressedSensingRadar.random_subdictionary_conditioning
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:02:16.3688+00:00
-- url     : https://prove2.me/theorems/6b66bba2-eaad-42bc-880c-d9a11675e244
-- title:
--   Proposition 1 (Tropp, Theorem B): random subdictionaries are well conditioned
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $\Phi\in\mathbb{C}^{N\times N^2}$ have unit-norm atoms and coherence $\mu$. Let $1\le K\le N^2$, and let $X=\Phi_T$ be a random $K$-column subdictionary, every $K$-column subset being equally likely. If $\vartheta\ge1$ and
--
--   $$\sqrt{\mu^2K\log K\cdot\vartheta}+\frac{K}{N^2}\|\Phi\|^2\le c\,\delta,$$
--
--   then
--
--   $$\mathbb{P}\{\|X^*X-I\|\ge\delta\}\le K^{-\vartheta},$$
--
--   where $\|\cdot\|$ is the spectral norm.
--
--   **Formalization Note** Tropp's Theorem B has $\log(K+1)$ where the paper has $\log K$. Because $c$ is only asserted to exist, the paper's version follows from Tropp's after shrinking $c$.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Appendix A, Proposition 1, pp. 12-13 (citing Tropp, On the conditioning of random subdictionaries, 2008, Theorem B)

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem random_subdictionary_conditioning :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (Φ : Matrix (Fin N) (Fin (N ^ 2)) ℂ), HasUnitAtoms Φ →
      ∀ K : ℕ, 1 ≤ K → K ≤ N ^ 2 → ∀ δ ϑ : ℝ, 1 ≤ ϑ →
        Real.sqrt (coherence Φ ^ 2 * K * Real.log K * ϑ) +
            (K : ℝ) / (N : ℝ) ^ 2 * specNorm Φ ^ 2 ≤ c * δ →
          illCondProb Φ K δ ≤ (K : ℝ) ^ (-ϑ) := by sorry

end CompressedSensingRadar
