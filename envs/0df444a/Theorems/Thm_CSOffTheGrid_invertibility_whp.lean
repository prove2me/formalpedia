-- Prove2me | Theorems.Thm_CSOffTheGrid_invertibility_whp
-- name    : CSOffTheGrid.invertibility_whp
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:26:24.180231+00:00
-- url     : https://prove2.me/theorems/ae4e68d6-b8b1-4768-a967-0479aea312fb
-- title:
--   Lemma 4.4: the random system matrix concentrates
-- statement:
--   Let $f_1,\dots,f_s\in[0,1]$ satisfy $\Delta_f\ge1/M$, let $0<m<M$ and $p=m/M$. Observe the entries of $J=\{-2M,\dots,2M\}$ independently with probability $p$, let $T$ be the observed set, and let $D$ be the system matrix of the random kernel $K_M(f)=\frac1M\sum_{j\in T}g_M(j)e^{-i2\pi fj}$ (normalized by the deterministic $|\bar K_M''(0)|$). If $\tau\in(0,0.6377)$, $\delta\in(0,1)$ and
--
--   $$m\ge\frac{50}{\tau^2}\,s\log\frac{2s}{\delta},$$
--
--   then
--
--   $$\mathbb P\big(\|p^{-1}D-\bar D\|\le\tau\big)\ge1-\delta.$$
--
--   **Formalization Note** The separation $\Delta_f\ge1/M$ is the standing assumption of Section 4, and the Bernoulli model with $p=m/M<1$ is the one of Section 4.2. The proof uses $\|\bar D\|\le1.3623$ from Proposition 4.1 and $M\ge4$. The sample condition already forces $M>85$ when $s\ge1$, and the case $s=0$ is trivial.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 4.4, Lemma 4.4, eq. (4.26), p. 22; proof in Appendix D, pp. 43-44

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem invertibility_whp (M : ℕ) {s : ℕ} (f : Fin s → ℝ)
    (hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1) (hsep : IsSeparated f (1 / (M : ℝ)))
    (m : ℕ) (hm0 : 0 < m) (hmM : m < M) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 0.6377)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 50 / τ ^ 2 * s * Real.log (2 * s / δ) ≤ m) :
    1 - δ ≤ bernoulliProb (symJ M) ((m : ℝ) / M)
      (fun T => opNorm (((M : ℂ) / m) • sysMat M T f - sysMatBar M f) ≤ τ) := by sorry

end CSOffTheGrid
