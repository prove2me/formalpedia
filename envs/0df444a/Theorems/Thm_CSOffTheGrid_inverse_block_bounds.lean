-- Prove2me | Theorems.Thm_CSOffTheGrid_inverse_block_bounds
-- name    : CSOffTheGrid.inverse_block_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:26:55.416798+00:00
-- url     : https://prove2.me/theorems/82a92c74-2e7a-4d69-8c06-09939f15f32d
-- title:
--   Corollary 4.5: bounds on the blocks of the inverse system matrix
-- statement:
--   Let $f_1,\dots,f_s\in[0,1]$ satisfy $\Delta_f\ge1/M$, let $0<m<M$, $p=m/M$, and let $T\subseteq\{-2M,\dots,2M\}$. Let $\tau\in(0,\tfrac14]$ and suppose that the event $\mathcal E_{1,\tau}$ holds: $\|p^{-1}D-\bar D\|\le\tau$. Then $D$ is invertible and, writing $\bar D^{-1}=[\bar L\ \bar R]$ and $D^{-1}=[L\ R]$ with $L,\bar L$ of size $2s\times s$,
--
--   $$\|L-p^{-1}\bar L\|\le2\|\bar D^{-1}\|^2p^{-1}\tau,\qquad\|L\|\le2\|\bar D^{-1}\|p^{-1}.$$
--
--   **Formalization Note** The invertibility of $D$ on $\mathcal E_{1,\tau}$ is stated in the paper right after Lemma 4.4 and is included in the conclusion, because $L$ is defined from $D^{-1}$. The proof uses $\|\bar D^{-1}\|\le1.568$ from Proposition 4.1. The separation $\Delta_f\ge1/M$ is the standing assumption of Section 4, and $0<m<M$ forces $M\ge2$.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 4.4, Corollary 4.5, p. 22; proof in Appendix E, p. 44

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem inverse_block_bounds (M : ℕ) {s : ℕ} (f : Fin s → ℝ)
    (hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1) (hsep : IsSeparated f (1 / (M : ℝ)))
    (m : ℕ) (hm0 : 0 < m) (hmM : m < M) (T : Finset ℤ) (hT : T ⊆ symJ M)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 4)
    (hE : opNorm (((M : ℂ) / m) • sysMat M T f - sysMatBar M f) ≤ τ) :
    (sysMat M T f).det ≠ 0 ∧
      opNorm (leftBlock (sysMat M T f)⁻¹ - ((M : ℂ) / m) • leftBlock (sysMatBar M f)⁻¹) ≤
        2 * opNorm (sysMatBar M f)⁻¹ ^ 2 * ((M : ℝ) / m) * τ ∧
      opNorm (leftBlock (sysMat M T f)⁻¹) ≤ 2 * opNorm (sysMatBar M f)⁻¹ * ((M : ℝ) / m) := by sorry

end CSOffTheGrid
