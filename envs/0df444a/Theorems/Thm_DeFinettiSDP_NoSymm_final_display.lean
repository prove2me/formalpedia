-- Prove2me | Theorems.Thm_DeFinettiSDP_NoSymm_final_display
-- name    : DeFinettiSDP.NoSymm.final_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:47:31.380434+00:00
-- url     : https://prove2.me/theorems/2b48ddfe-1a57-4eb8-af3f-54d7dc02c3a4
-- title:
--   Proof of Theorem 2.5, p. 11 — average product error bound
-- statement:
--   Let $\rho$ be any state on $n=k+r$ copies of $B$, with $k\ge1$, and let $M$ be any finite-outcome measurement on $B$. Write $E_m(\rho,M)$ for the expected trace-norm error between the conditional state of the $k$ randomly retained systems and the tensor product of its one-system marginals after measuring $m$ of the other systems. If $D(M)$ is the fixed measurement's side-information distortion, then
--
--   $$
--   \frac1{r+1}\sum_{m=0}^{r}E_m(\rho,M)
--   \le kD(M)\sqrt{\frac{(2\ln2)\log_2(d_B^{k-1})}{r+1}}.
--   $$
--
--   This is the outer inequality of the last display in the proof of Theorem 2.5. Averaging over $m$ prepares the existence conclusion of the theorem.
--
--   **Formalization Note** The paper writes $f(B\mid\cdot)$ after choosing a suitable measurement. This item works for every fixed POVM and uses its own, possibly infinite, distortion. The inequality is represented in extended nonnegative reals. The paper's $n-k+1$ is $r+1$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, proof of Theorem 2.5, p. 11, first display

import Mathlib
import Definitions.Def_DeFinettiSDP_NoSymm_Random

namespace DeFinettiSDP.NoSymm

/-- Last display of the proof of Theorem 2.5, p. 11: its outer inequality only.
The paper's `n` is `k+r`; its average over `m=0,…,n-k` is over `0,…,r`.
The factor `distortion M` is the fixed measurement's loss; it may be infinite. -/
theorem final_display {dB t : ℕ} (k r : ℕ) (hk : 1 ≤ k)
    (ρ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (hM : DeFinettiSDP.Hierarchy.IsPOVM M) :
    ENNReal.ofReal
        ((1 / ((r : ℝ) + 1)) * ∑ m ∈ Finset.range (r + 1), rsError k r ρ M m) ≤
      (k : ENNReal) * DeFinettiSDP.Hierarchy.distortion M *
        ENNReal.ofReal
          (Real.sqrt (2 * Real.log 2 *
            Real.logb 2 ((dB : ℝ) ^ (k - 1)) / ((r : ℝ) + 1))) := by sorry

end DeFinettiSDP.NoSymm
