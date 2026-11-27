-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_readSeed_exec
-- name    : DirectedHamiltonicity.Main.CycleHost.readSeed_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:01:51.825046+00:00
-- url     : https://prove2.me/theorems/53675a99-3ef7-4728-ab12-dbdcee76f281
-- title:
--   Host sub-routine: reading one seed block
-- statement:
--   Specification of the sub-routine `readSeed`.
--
--   For trial $i$ and seed width $w$, the routine reads the coins at positions $iw,\dots,iw+w-1$ (a missing coin reads as $0$) and leaves in register $D$ the number
--   $$D=\sum_{j<w} c_{iw+j}\,2^{j},$$
--   using at most $100(w+1)+10(b+1)^2$ steps at a word width $b$ that accommodates the positions and $2^{w}$. Only its listed scratch registers change.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search: specification of a sub-routine of the host program in Def_DirectedHamiltonicity_CycleSearchHost, supporting Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 (PDF pp. 4-5).

import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost

theorem DirectedHamiltonicity.Main.CycleHost.readSeed_exec {τ : Tapes} {b : ℕ} (u : Store) (i sw : ℕ)
    (c : Consts u) (ri : u.mem (cell rI) = i) (rsw : u.mem (cell rSw) = sw)
    (fit : u.Fits b) (hb : (i * sw + sw).size + sw + 4 ≤ b) (hi : (2 * i + 2).size ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) readSeed u v j ∧ j ≤ 100 * (sw + 1) + 10 * (b + 1) ^ 2 ∧
      v.mem (cell rDv) = ∑ j : Fin sw, (τ.coins[i * sw + j.val]?.getD false).toNat * 2 ^ j.val ∧
      Kept readSeedDirty u v (fun _ => True) := by sorry
