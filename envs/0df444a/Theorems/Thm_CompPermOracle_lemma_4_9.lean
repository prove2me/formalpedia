-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_9
-- name    : CompPermOracle.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:55.924144+00:00
-- url     : https://prove2.me/theorems/410c38c0-17dd-4a66-b247-7667df84a0c1
-- title:
--   Lemma 4.9 — $\mathcal H_r$ is a sum of Specht blocks, on which $G_r$ acts by $g_{m,\mu}$
-- statement:
--   Let $0\le r\le N-1$ and $m=N-r$. The space $\mathcal H_r$ is the direct sum of the blocks $S^\lambda\otimes S^\lambda$ of the group algebra with $\lambda_1=m$. If $\lambda=(m,\mu)$ on such a block, then $G_r$ acts by
--   $$
--   g_{m,\mu}=\frac{1}{m!}\prod_{c=1}^{m}(m-c+1+\mu'_c)=\prod_{c=1}^{m}\Big(1+\frac{\mu'_c}{m-c+1}\Big).
--   $$
--   In particular, on $\mathcal H_r$,
--   $$
--   \lambda_{\min}(G_r)=\frac{N}{N-r},\qquad \|G_r^{-1}\|=\frac{N-r}{N}\le1.
--   $$
--   If $r\le(N-1)/2$, then $\|G_r\|\le\exp\big(r/(N-2r+1)\big)$. Consequently, for $s\le(N-1)/2$,
--   $$
--   \|(\tilde V-V)\Pi_s\|\le\frac{s}{2(N-2s+1)}.
--   $$
--   This is the spectral input: it shows that $G_r$ is close to the identity at low levels, so that $\tilde V$ and $V$ are close.
--
--   **Formalization Note** The last display is eq. (30) of the source.
--
--   Differences from the source:
--   - reading: $\lambda_{\min}(G_r)$, $\|G_r^{-1}\|$ → the least eigenvalue on $\mathcal H_r$ (a lower bound on $\langle v,G_rv\rangle$ for $v\in\mathcal H_r$, attained by a nonzero $v$), and the norm of the inverse on $\mathcal H_r$ extended by $0$; reason: $G_r$ vanishes off $\mathcal H_r$; the source says it is invertible on $\mathcal H_r$ (p.12)
--   - encoding: the direct sum of the blocks in (32), $\lambda\vdash N$, $S^\lambda\otimes S^\lambda$ → supremum of pairwise orthogonal `componentSpace (regularRep _) (index λ)` over `Shape N`; reason: the left isotypic component of type $S^\lambda$ of $\mathbb C[S_N]$ is the two-sided block
--   - encoding: $\mu'_c$, $c=1,\dots,m$; $r,s\le(N-1)/2$ → `colLen c' - 1`, $c'=c-1$; $2r+1\le N$, $2s+1\le N$; reason: the same numbers
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.9, p.17; eq. (30), p.16

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_spechtBlock

namespace CompPermOracle

open OAI.PartialPermutation.DiagramCounting

/-- Lemma 4.9 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.17), with `m = N − r`: `ℋ_r` is the direct sum of the blocks
of eq. (32) with `λ_1 = m`; `G_r` acts on such a block by `g_{m,μ}` (33), in both printed forms; (34);
(35); and (30).

**Formalization Note.** `0 ≤ r ≤ N − 1` is `r < N`, and `m = N − r` is an exact natural subtraction.
The direct sum is the supremum plus pairwise orthogonality. `G_r` vanishes off `ℋ_r`, so `λ_min(G_r)`
in (34) is the least eigenvalue of `G_r` on `ℋ_r`, written as a lower bound with equality attained on
a nonzero vector, and `G_r^{−1}` is the inverse on `ℋ_r` extended by `0` (`GramInv`). `r ≤ (N − 1)/2`
and `s ≤ (N − 1)/2` are `2r + 1 ≤ N` and `2s + 1 ≤ N`. -/
theorem lemma_4_9 {N r : ℕ} (hr : r < N) :
    (Hlevel N r = ⨆ (lam : Shape N) (_ : firstRow lam = N - r), block lam) ∧
    (∀ lam lam' : Shape N, firstRow lam = N - r → firstRow lam' = N - r → lam ≠ lam' →
      (block lam) ⟂ (block lam')) ∧
    (∀ lam : Shape N, firstRow lam = N - r → ∀ v ∈ block lam,
      Gram N r v = ((gramEig lam : ℝ) : ℂ) • v) ∧
    (∀ lam : Shape N, firstRow lam = N - r →
      ((firstRow lam).factorial : ℝ)⁻¹ * ∏ c ∈ Finset.range (firstRow lam),
          ((firstRow lam : ℝ) - (c : ℝ) + ((lam.1.colLen c - 1 : ℕ) : ℝ)) = gramEig lam) ∧
    (∀ v ∈ Hlevel N r,
      ((N : ℝ) / ((N : ℝ) - r)) * ‖v‖ ^ 2 ≤ (inner ℂ v (Gram N r v)).re) ∧
    (∃ v ∈ Hlevel N r, v ≠ 0 ∧
      (inner ℂ v (Gram N r v)).re = ((N : ℝ) / ((N : ℝ) - r)) * ‖v‖ ^ 2) ∧
    ‖GramInv N r‖ = ((N : ℝ) - r) / N ∧
    ((N : ℝ) - r) / N ≤ 1 ∧
    (2 * r + 1 ≤ N → ‖Gram N r‖ ≤ Real.exp ((r : ℝ) / ((N : ℝ) - 2 * r + 1))) ∧
    (∀ s : ℕ, 2 * s + 1 ≤ N →
      ‖(Vtmap N - Vmap N).comp (ProjLevel N s)‖ ≤ (s : ℝ) / (2 * ((N : ℝ) - 2 * s + 1))) := by sorry

end CompPermOracle
