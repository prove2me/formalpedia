-- Prove2me | Theorems.Thm_CompressedSensingRadar_matrix_recovery_guaranteed
-- name    : CompressedSensingRadar.matrix_recovery_guaranteed
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:56:38.51822+00:00
-- url     : https://prove2.me/theorems/2bac8678-d2a0-493e-b6fc-3c0ad5b3d978
-- title:
--   Theorem 1: guaranteed recovery for $K<\frac12(\sqrt N+1)$
-- statement:
--   Let $N\ge5$ be prime. Suppose $H=\sum_is_iH_i\in\mathbb{C}^{N\times N}$ has a $K$-sparse representation $s\in\mathbb{C}^{N^2}$ in the time-frequency basis, with
--
--   $$K<\tfrac12\big(\sqrt N+1\big),$$
--
--   and that $y=Hf_A$ is observed. Then $s$ is the unique solution of basis pursuit $\min\|s'\|_1$ subject to $\Phi_As'=y$, and orthogonal matching pursuit applied to $y$ and $\Phi_A$ recovers $s$.
--
--   In radar terms, a scene of fewer than $\frac12(\sqrt N+1)$ targets on the $N\times N$ delay-Doppler grid is always identified exactly from one Alltop pulse.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section III-E, Theorem 1, p. 5; proof in Appendix A-A, p. 13

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem matrix_recovery_guaranteed (N : ℕ) (hN : N.Prime) (h5 : 5 ≤ N) (K : ℕ)
    (s : Fin (N ^ 2) → ℂ) (hs : IsSparse K s) (hK : (K : ℝ) < (Real.sqrt N + 1) / 2) :
    BPRecovers (gaborDict N (alltop N)) ((tfSynth N s).mulVec (alltop N)) s ∧
    OMPRecovers (gaborDict N (alltop N)) ((tfSynth N s).mulVec (alltop N)) s := by sorry

end CompressedSensingRadar
