-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_params_exec
-- name    : DirectedHamiltonicity.Main.CycleHost.params_exec
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T04:01:50.388667+00:00
-- url     : https://prove2.me/theorems/f6297b0d-62ec-4336-b174-ff6cd4454a5f
-- title:
--   Host sub-routine: computing the search parameters
-- statement:
--   Specification of the sub-routine `params`.
--
--   For $n\ge 2$ and constants $A,k$, the routine computes the parameters of the finite cycle search: $n^2$, $3n^2$, $W_{\max}(n)$, $B_{\max}(n)+1$, the number of draws, the number of trials, the seed width $\lceil\log_2(\#\text{draws})\rceil$, the parity-string length
--   $$L=A\,\bigl\lceil (15/8)^n\bigr\rceil\,(n+3n^2+6(n-1)+1)^k,$$
--   the majority size, and the memory layout (instance region, visited array, log and simulated memory). It uses at most $10^4(n+1)^2(k+1)(b+1)^2$ steps at word width $b\ge 1000(n+1)^3(k+1)+2\,\mathrm{size}(A)$ and changes only its listed registers.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search: specification of a sub-routine of the host program in Def_DirectedHamiltonicity_CycleSearchHost, supporting Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 (PDF pp. 4-5).

import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost

theorem DirectedHamiltonicity.Main.CycleHost.params_exec {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n) (A k : ℕ)
    (c : Consts u) (rn : u.mem (cell rN) = n) (ra : u.mem (cell rA) = A) (rk : u.mem (cell rKk) = k)
    (fit : u.Fits b) (hb : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) params u v j ∧ j ≤ 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 ∧
      v.mem (cell rN2) = n * n ∧ v.mem (cell rM) = 3 * (n * n) ∧ v.mem (cell rW) = Wmax n ∧
      v.mem (cell rBm1) = Bmax n + 1 ∧ v.mem (cell rPW) = Wmax n ^ (n * 3) ∧
      v.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1) ∧
      v.mem (cell rDc) = drawCount n ∧ v.mem (cell rTrials) = trials n ∧
      v.mem (cell rSw) = seedWidth n ∧ v.mem (cell rL) = coinSpan A k n ∧
      v.mem (cell rR) = majorityHalf n ∧ v.mem (cell rR2) = 2 * majorityHalf n ∧
      v.mem (cell rTapeBase) = trials n * seedWidth n ∧
      v.mem (cell rVB) = xBase + 128 * (n + 1) ^ 3 ∧
      v.mem (cell 103) = xBase + 128 * (n + 1) ^ 3 + n ∧
      v.mem (cell 102) = xBase + 128 * (n + 1) ^ 3 + n + coinSpan A k n + 1 ∧
      v.mem (cell 105) = xBase ∧ v.mem (cell 110) = 1 ∧ v.mem (cell 111) = 0 ∧
      Kept paramsDirty u v (fun _ => True) := by sorry
