-- Prove2me | Theorems.Thm_CompressedSensingRadar_tf_shifts_orthogonal_basis
-- name    : CompressedSensingRadar.tf_shifts_orthogonal_basis
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:42:44.062894+00:00
-- url     : https://prove2.me/theorems/3642e961-7e70-4f6c-a393-dd7443bfe84f
-- title:
--   Eq. (10) (corrected): the time-frequency shifts form an orthogonal basis of norm $\sqrt N$
-- statement:
--   Let $N\ge1$. Each time-frequency shift $H_i=M^{i\bmod N}T^{\lfloor i/N\rfloor}$, $0\le i<N^2$, is unitary, and the family is orthogonal for the Frobenius inner product with $\|H_i\|_F^2=N$:
--
--   $$\langle H_i,H_{i'}\rangle_F=\operatorname{trace}(H_i^*H_{i'})=N\,\delta_{ii'}.$$
--
--   Hence every $H\in\mathbb{C}^{N\times N}$ has the expansion $H=\sum_is_iH_i$ of eq. (6) with $s_i=\frac1N\langle H_i,H\rangle_F$. For every probe $f$ the observation is $Hf=\sum_is_iH_if=\Phi s$ (eq. 7).
--
--   This is the representation of an unknown system, such as a radar scene, by its coefficients in the time-frequency shift basis.
--
--   **Formalization Note** The paper states that $(H_i)$ is an orthonormal basis. Since $H_i$ is unitary, $\|H_i\|_F^2=\operatorname{trace}(I)=N$, so the family is orthogonal but not normalised. The statement gives the correct normalisation: the orthonormal basis is $(H_i/\sqrt N)$.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section III-A, eqs. (6)-(8), p. 3, and Section III-C, eq. (10), p. 3

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem tf_shifts_orthogonal_basis (N : ℕ) (hN : 0 < N) :
    (∀ i : Fin (N ^ 2), (tfShift N i).conjTranspose * tfShift N i = 1) ∧
    (∀ i i' : Fin (N ^ 2),
      frobIp N (tfShift N i) (tfShift N i') = if i = i' then (N : ℂ) else 0) ∧
    (∀ H : Matrix (Fin N) (Fin N) ℂ,
      H = tfSynth N (fun i => (N : ℂ)⁻¹ * frobIp N (tfShift N i) H)) ∧
    (∀ (s : Fin (N ^ 2) → ℂ) (f : Fin N → ℂ),
      (tfSynth N s).mulVec f = (gaborDict N f).mulVec s) := by sorry

end CompressedSensingRadar
