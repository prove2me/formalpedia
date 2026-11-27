-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_decodeDraw_exec
-- name    : DirectedHamiltonicity.Main.CycleHost.decodeDraw_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:01:33.287875+00:00
-- url     : https://prove2.me/theorems/8e8f3613-8ce3-53bf-ab1e-a58dbd54e9ec
-- title:
--   Host sub-routine: decoding a draw rank
-- statement:
--   Specification of the sub-routine `decodeDraw`.
--
--   For $n\ge 2$ and a rank $D$ below the number of draws, the routine computes by integer division the components of the draw $d=\mathrm{rankDraw}_n^{-1}(D)$: the endpoints $s,t$, the target weight $B$, and two integers whose base-$50$ and base-$W_{\max}(n)$ digits are the arc-symbol and group-weight tables of $d$. It uses at most $100(b+1)^2$ steps at word width $b\ge 64(n+1)^3$ and changes only its listed registers.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search: specification of a sub-routine of the host program in Def_DirectedHamiltonicity_CycleSearchHost, supporting Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 (PDF pp. 4-5).

import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost

theorem DirectedHamiltonicity.Main.CycleHost.decodeDraw_exec {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n) (D : ℕ)
    (hD : D < drawCount n)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rdv : u.mem (cell rDv) = D)
    (rin : u.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1))
    (rbm : u.mem (cell rBm1) = Bmax n + 1) (rpw : u.mem (cell rPW) = Wmax n ^ (n * 3))
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    let d := (rankDraw n).symm ⟨D, hD⟩
    ∃ v j, Exec τ (fun w => w.Fits b) decodeDraw u v j ∧ j ≤ 100 * (b + 1) ^ 2 ∧
      v.mem (cell rS) = d.1.1.val ∧ v.mem (cell rT) = d.1.2.val ∧ v.mem (cell rB) = d.2.2.val ∧
      v.mem (cell rSym) < 50 ^ (n * n) ∧ v.mem (cell rWt) < Wmax n ^ (n * 3) ∧
      (∀ x y : Fin n, v.mem (cell rSym) / 50 ^ (x.val * n + y.val) % 50 = (d.2.1.1 (x, y)).val) ∧
      (∀ (y : Fin n) (l : Fin 3),
        v.mem (cell rWt) / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (d.2.1.2 (y, l)).val) ∧
      Kept decodeDirty u v (fun _ => True) := by sorry
