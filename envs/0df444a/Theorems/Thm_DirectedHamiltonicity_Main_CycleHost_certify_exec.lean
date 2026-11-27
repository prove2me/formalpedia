-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_certify_exec
-- name    : DirectedHamiltonicity.Main.CycleHost.certify_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:01:24.439797+00:00
-- url     : https://prove2.me/theorems/71e8a75b-efd5-5025-9a95-efc22ed8768d
-- title:
--   Host sub-routine: the final Hamiltonian-cycle check
-- statement:
--   Specification of the sub-routine `certify`, the final cycle check of the host program.
--
--   Let $n\ge 2$ and let $R$ be a set of arcs packed into $G<2^{n^2}$ (bit $un+v$ is set iff $(u,v)\in R$). With a zero visited array of length $n$ at a base address $V_B\ge 214$ and word width $b\ge 64(n+1)^3$, the routine runs for at most $10^6(n+1)^4(b+1)^2$ steps and appends to the output the bit
--   $$\mathrm{certify}(n,R),$$
--   which states that following the first outgoing arc from vertex $0$ visits all $n$ vertices along arcs of $R$ and returns to $0$. Only listed scratch registers and the visited array change.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search: specification of a sub-routine of the host program in Def_DirectedHamiltonicity_CycleSearchHost, supporting Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 (PDF pp. 4-5).

import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost

theorem DirectedHamiltonicity.Main.CycleHost.certify_exec {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n)
    (R : Finset (Fin n × Fin n)) (G VB : ℕ) (hG : G < 2 ^ (n * n))
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = decide ((x, y) ∈ R))
    (c : Consts u) (rn : u.mem (cell rN) = n) (rg : u.mem (cell rG) = G) (rvb : u.mem (cell rVB) = VB)
    (hVB : cell 200 ≤ VB) (vis : ∀ i < n, u.mem (VB + i) = 0)
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) (hvb : (VB + n).size + 2 ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) certify u v j ∧ j ≤ 10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 ∧
      v.out = u.out ++ [CycleReduction.certify n R] ∧
      ∀ a, 14 ≤ a → (∀ d ∈ certifyDirty, a ≠ cell d) → (a < VB ∨ VB + n ≤ a) → v.mem a = u.mem a := by sorry
