-- Prove2me | Theorems.Thm_CompressedSensingRadar_coherence_exact_recovery
-- name    : CompressedSensingRadar.coherence_exact_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:51:37.79658+00:00
-- url     : https://prove2.me/theorems/d86024a4-330f-4383-8cd5-bc63bc3b78d5
-- title:
--   Appendix A-A (Tropp 2004, Theorem B): exact recovery by BP and OMP when $K<\frac12(\mu^{-1}+1)$
-- statement:
--   Let $\Phi\in\mathbb{C}^{n\times M}$ have unit-norm atoms and coherence $\mu$. Let $s\in\mathbb{C}^M$ be $K$-sparse with
--
--   $$K<\tfrac12\big(\mu^{-1}+1\big),$$
--
--   and set $y=\Phi s$. Then:
--
--   1. $s$ is the unique sparsest representation of $y$: every $s'\ne s$ with $\Phi s'=y$ has $\|s'\|_0>\|s\|_0$;
--   2. $s$ is the unique solution of basis pursuit for $y$;
--   3. orthogonal matching pursuit recovers $s$ from $y$ in $\|s\|_0$ steps, whatever choice it makes among tied indices.
--
--   This is the general-dictionary result the paper quotes from Tropp to prove Theorem 1.
--
--   **Formalization Note** The sparsity condition is written $2K\mu<1+\mu$. This is equivalent to $K<\frac12(\mu^{-1}+1)$ when $\mu>0$, and it reads $K<\infty$ when $\mu=0$.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Appendix A-A, proof of Theorem 1, p. 13 (citing Tropp, Greed is good, IEEE Trans. Inf. Theory 50 (2004), Theorem B)

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem coherence_exact_recovery {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℂ) (hΦ : HasUnitAtoms Φ)
    (K : ℕ) (hK : 2 * (K : ℝ) * coherence Φ < 1 + coherence Φ)
    (s : Fin M → ℂ) (hs : IsSparse K s) :
    (∀ s' : Fin M → ℂ, Φ.mulVec s' = Φ.mulVec s → s' ≠ s → suppCard s < suppCard s') ∧
    BPRecovers Φ (Φ.mulVec s) s ∧ OMPRecovers Φ (Φ.mulVec s) s := by sorry

end CompressedSensingRadar
