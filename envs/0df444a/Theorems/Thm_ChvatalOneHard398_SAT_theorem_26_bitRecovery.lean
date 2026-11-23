-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_theorem_26_bitRecovery
-- name    : ChvatalOneHard398.SAT.theorem_26_bitRecovery
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:19:46.155728+00:00
-- url     : https://prove2.me/theorems/dc949d52-1f57-4968-98e6-f2f586bc541c
-- title:
--   Theorem 26 — binary coordinate recovery invariant
-- statement:
--   This is the arithmetic induction used to recover each coefficient in the proof of Theorem 26. Let $d$ be the nonnegative displacement $y_i^*-c_i$, and define $u_0=0$ and
--   $$
--   u_{k+1}=\begin{cases}u_k,&d\bmod 2^{k+1}=u_k,\\u_k+2^k,&\text{otherwise.}\end{cases}
--   $$
--   Then every prefix is the correct binary residue,
--   $$u_k=d\bmod 2^k,$$
--   and consequently $d<2^K$ implies $u_K=d$. In the decoding algorithm, the two cases are distinguished by the satisfiability query for the scaled congruence lattice.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), pp.28–29, proof of Theorem 26, induction giving $u_{i,k}=(y_i^*-c_i)\bmod 2^k$ and $z_i=y_i^*$; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib

namespace ChvatalOneHard398.SAT

/-- The bitwise invariant behind coordinate recovery in Theorem 26. -/
theorem theorem_26_bitRecovery (d : ℕ) (u : ℕ → ℕ)
    (h0 : u 0 = 0)
    (hstep : ∀ k, u (k+1) = if d % 2^(k+1) = u k then u k else u k + 2^k) :
    (∀ k, u k = d % 2^k) ∧ ∀ K, d < 2^K → u K = d := by sorry
