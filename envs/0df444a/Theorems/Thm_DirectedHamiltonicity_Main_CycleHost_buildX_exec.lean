-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_buildX_exec
-- name    : DirectedHamiltonicity.Main.CycleHost.buildX_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:01:49.732795+00:00
-- url     : https://prove2.me/theorems/7ebe730e-719d-42ce-ab0d-5d2bedf49450
-- title:
--   Host sub-routine: writing the weighted parity instance
-- statement:
--   Specification of the sub-routine `buildX`, which writes the weighted parity instance of a candidate draw into memory.
--
--   Let $n\ge 2$, let $\mathrm{adj}$ be an adjacency matrix on $n$ vertices, $s,t$ vertices, $z$ a table of arc symbols and group weights, and $B\le B_{\max}(n)$. Assume the registers hold $n$, $3n^2$, the packed adjacency bits $G<2^{n^2}$, $s$, $t$, $B$ and two integers whose base-$50$ and base-$W_{\max}(n)$ digits are the entries of $z$. Then `buildX` runs for at most $10^6(n+1)^6(b+1)^2$ steps at word width $b\ge 64(n+1)^3$ and writes the string
--   $$x=\mathrm{candX}(\mathrm{adj},s,t,z,B)$$
--   bit by bit from address $300$, records $|x|\le 128(n+1)^3$, and changes only its listed scratch registers and the instance region.
--
--   The string $x$ is exactly the parity-query input that the finite cycle search hands to the parity program.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search: specification of a sub-routine of the host program in Def_DirectedHamiltonicity_CycleSearchHost, supporting Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 (PDF pp. 4-5).

import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost

theorem DirectedHamiltonicity.Main.CycleHost.buildX_exec {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n)
    (adj : Fin n → Fin n → Bool) (s t : Fin n) (z : MatrixSeed n) (B : ℕ) (hB : B ≤ Bmax n)
    (G sym wt : ℕ) (hG : G < 2 ^ (n * n)) (hsym : sym < 50 ^ (n * n)) (hwt : wt < Wmax n ^ (n * 3))
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = adj x y)
    (symd : ∀ x y : Fin n, sym / 50 ^ (x.val * n + y.val) % 50 = (z.1 (x, y)).val)
    (wtd : ∀ (y : Fin n) (l : Fin 3), wt / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (z.2 (y, l)).val)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rm : u.mem (cell rM) = 3 * (n * n))
    (rg : u.mem (cell rGp) = G) (rs : u.mem (cell rS) = s.val) (rt : u.mem (cell rT) = t.val)
    (rb : u.mem (cell rB) = B) (rsym : u.mem (cell rSym) = sym) (rwt : u.mem (cell rWt) = wt)
    (rw : u.mem (cell rW) = Wmax n) (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    let x := candX adj s t z B
    ∃ v j, Exec τ (fun w => w.Fits b) buildX u v j ∧ j ≤ 10 ^ 6 * (n + 1) ^ 6 * (b + 1) ^ 2 ∧
      x.length ≤ 128 * (n + 1) ^ 3 ∧ v.mem (cell 106) = x.length ∧
      (∀ i (hi : i < x.length), v.mem (xBase + i) = (x[i]'hi).toNat) ∧
      Kept buildXDirty u v (fun a => a < xBase ∨ xBase + 128 * (n + 1) ^ 3 ≤ a) := by sorry
