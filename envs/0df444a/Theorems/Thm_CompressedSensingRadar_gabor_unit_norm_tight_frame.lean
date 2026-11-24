-- Prove2me | Theorems.Thm_CompressedSensingRadar_gabor_unit_norm_tight_frame
-- name    : CompressedSensingRadar.gabor_unit_norm_tight_frame
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:43:58.397632+00:00
-- url     : https://prove2.me/theorems/d17e442a-3d1a-4142-a8fe-4ad94e2ff8d8
-- title:
--   Section III-C, eq. (11): the Gabor dictionary of a unit vector is a unit-norm tight frame
-- statement:
--   Let $N\ge1$ and let $f\in\mathbb{C}^N$ with $\|f\|_2=1$. Let $\Phi$ be the Gabor dictionary of $f$, with atoms $\varphi_i=H_if$, $0\le i<N^2$. Then:
--
--   1. every atom has $\|\varphi_i\|_2=1$;
--   2. $\Phi$ is a tight frame, $\Phi\Phi^*=N\,I_N$, so that $\|\Phi\|^2=N$;
--   3. the $j$-th column of the block $D_kW_N$ of eq. (11) is the atom $\varphi_i$ with $\lfloor i/N\rfloor=(N-k)\bmod N$ and $i\bmod N=j$.
--
--   Item 2 is the value $\|\Phi_A\|^2=N$ used in the proof of Theorem 2.
--
--   **Formalization Note** Eq. (11) writes $\Phi=(\Phi^{(0)}|\cdots|\Phi^{(N-1)})$ with $\Phi^{(k)}=D_kW_N$, which puts the block $D_kW_N$ in columns $kN,\dots,kN+N-1$. Those columns are $M^jT^kf$, and $D_kW_N$ has columns $M^jT^{-k}f$. The two agree only for $k=0$. Item 3 records the correct correspondence. The blocks are the same set of $N$ bases, so Properties 1 and 2 are unaffected.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section III-C, eqs. (8) and (11), pp. 3-4; tight-frame property used in Appendix A-B, p. 13

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem gabor_unit_norm_tight_frame (N : ℕ) (hN : 0 < N) (f : Fin N → ℂ) (hf : norm2 f = 1) :
    HasUnitAtoms (gaborDict N f) ∧
    gaborDict N f * (gaborDict N f).conjTranspose = (N : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    specNorm (gaborDict N f) ^ 2 = N ∧
    (∀ (k j : Fin N) (i : Fin (N ^ 2)), (i : ℕ) / N = (N - (k : ℕ)) % N → (i : ℕ) % N = j →
      blockAtom N f k j = atom (gaborDict N f) i) := by sorry

end CompressedSensingRadar
