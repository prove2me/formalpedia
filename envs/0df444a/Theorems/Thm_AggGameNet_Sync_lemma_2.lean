-- Prove2me | Theorems.Thm_AggGameNet_Sync_lemma_2
-- name    : AggGameNet.Sync.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:36.686519+00:00
-- url     : https://prove2.me/theorems/f702d6b5-b3a6-4c32-bf90-5df35218303e
-- title:
--   Lemma 2, p. 10 — the mean estimate equals the true mean decision
-- statement:
--   Let $N\ge1$. If every matrix $W(k)$ has unit column sums, the estimates start at $v_i^0=x_i^0$, and they obey $v_i^{k+1}=\sum_jw_{ij}(k)v_j^k+x_i^{k+1}-x_i^k$, then for every $k\ge0$,
--
--   $$y^k:=\frac1N\sum_i v_i^k=\frac1N\sum_i x_i^k.$$
--
--   This identity lets the analysis replace the network-wide average estimate with the actual average decision. It needs no projection or graph hypothesis.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 2, p. 10

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

/-- Lemma 2, p. 10: column-stochastic averaging preserves the actual mean. -/
theorem lemma_2 {N n : ℕ} (hN : 0 < N)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (x v : ℕ → Fin N → E n)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hinit : v 0 = x 0)
    (hrec : ∀ k i, v (k + 1) i = vhat W v k i + x (k + 1) i - x k i) :
    ∀ k, yavg v k = (1 / (N : ℝ)) • ∑ i, x k i := by sorry

end AggGameNet.Sync
