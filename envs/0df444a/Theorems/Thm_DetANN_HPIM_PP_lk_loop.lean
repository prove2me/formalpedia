-- Prove2me | Theorems.Thm_DetANN_HPIM_PP_lk_loop
-- name    : DetANN.HPIM.PP.lk_loop
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T09:26:58.071146+00:00
-- url     : https://prove2.me/theorems/074aa32e-3eff-4429-9a7d-091a292ac5f2
-- title:
--   The lookup loop of a node
-- statement:
--   Let $B$ be blocks with `Blocks.WF` and `ChildOK B`, $m\ge1$ and $\delta\in(0,1/2)$. Let $S$ be a node with $|S|\ge2$ and ladder length $M=M(S)$ (definition `DetANN_HPIMTree`). Assume:
--   - the run is at LK in iteration $i$, with $i+d=M$, the node frame (`NodeEnv`), and the ladder radius $\rho_i$ in a register;
--   - the lookups $Z_{i'}$ for $i'<i$ are already stored (`BoxTreeAt`) through the array at $Z_{arr}$.
--
--   Then the run reaches LKE with the frame intact. All $M$ lookups $Z_{i'}=\mathrm{lookupTree}(P,\rho_{i'},1+\delta/4)$ are stored through the array, each stably under changes outside the new heap cells. Moreover:
--   - the integer heap grows by at most $d\cdot\mathrm{lkH}$ and the real heap by $d\cdot\mathrm{lkR}$;
--   - the work is at most $d\cdot\mathrm{lkW}$;
--   - only the new heap, the array and bounded scratch windows are written.
--
--   Each iteration builds the root box, runs `build` with fuel `bspFuel` (it does not starve, by `build_size`), runs `balance`, and adds the root test node. This is the inner loop of the node contract (definition `DetANN_HPIMPreProg`).
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the intermediate steps of the reduction of DetANN.HPIM.hpim_preprocessing, split so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

lemma lk_loop (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (v Sa Zn ZRn Zarr Hl0 HR0 : ℤ) (M : ℕ)
    (hM : M = MOf Y δ S) (hρpos : ∀ k, 0 < rhoOf Y δ S k) (hZn : Zn ≤ 0) (hZRn : ZRn ≤ 0)
    (hHR : 1 + N * m ≤ HR0) (hZH : Zarr + M ≤ Hl0) (hH0 : 0 ≤ Zarr) (hHb : Hbase N T0 ≤ Sa)
    (hSZ : Sa + S.card ≤ Zarr) :
    ∀ d i, (hid : i + d = M) → ∀ s : State, s.core.pc = B.lbl_LK → s.halted = false →
      NodeEnv Y δ T0 v0 S v Sa Zn ZRn s → s.core.ptrs 3 = i → s.core.ptrs 4 = M →
      s.core.ptrs 18 = Zarr → s.core.ptrs 13 = Zn → s.core.ptrs 14 = ZRn →
      s.core.regs 4 = rhoOf Y δ S i →
      Hl0 ≤ s.core.ptrs 15 → HR0 ≤ s.core.ptrs 16 →
      (∀ i' (hi' : i' < i), ∀ s'' : State,
        (∀ z, Hl0 ≤ z → z < s.core.ptrs 15 → s''.integerMemory z = s.integerMemory z) →
        (∀ z, HR0 ≤ z → z < s.core.ptrs 16 → s''.core.mem z = s.core.mem z) →
        BoxTreeAt m s'' (s.integerMemory (Zarr + i')) (ZOf Y δ S ⟨i', hM ▸ (by omega)⟩)) →
      ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.o11 ∧
        (run (Blocks.prog B) s detTape t).halted = false ∧
        NodeEnv Y δ T0 v0 S v Sa Zn ZRn (run (Blocks.prog B) s detTape t) ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 13 = Zn ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 14 = ZRn ∧
        (∀ x < 40, x ∉ [0, 3, 6, 7, 13, 14, 15, 16, 17, 22, 27, 29, 31] →
          (run (Blocks.prog B) s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x < 40, x ∉ [4, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] →
          (run (Blocks.prog B) s detTape t).core.regs x = s.core.regs x) ∧
        (run (Blocks.prog B) s detTape t).core.regs 10 = s.core.regs 21 * s.core.regs 3 ∧
        s.core.ptrs 15 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 15 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + d * lkH ch S.card m δ ∧
        s.core.ptrs 16 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + d * lkR ch S.card m δ ∧
        (∀ i' (hi' : i' < M), ∀ s'' : State,
          (∀ z, Hl0 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 15 →
            s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
          (∀ z, HR0 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
            s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
          BoxTreeAt m s'' ((run (Blocks.prog B) s detTape t).integerMemory (Zarr + i'))
            (ZOf Y δ S ⟨i', hM ▸ hi'⟩)) ∧
        (∀ z, z < Zarr ∨ (Zarr + M ≤ z ∧ z < s.core.ptrs 15) →
          0 ≤ z → (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ z, 0 ≤ z → z < s.core.ptrs 16 → (run (Blocks.prog B) s detTape t).core.mem z = s.core.mem z) ∧
        (∀ c ∈ cellsWritten (Blocks.prog B) s t,
          (c.1 = false ∧ ((s.core.ptrs 15 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 15) ∨
            (Zarr ≤ c.2 ∧ c.2 < Zarr + M) ∨ (Zn - lkD ch S.card m δ ≤ c.2 ∧ c.2 < Zn))) ∨
          (c.1 = true ∧ ((s.core.ptrs 16 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
            (ZRn - lkD ch S.card m δ ≤ c.2 ∧ c.2 < ZRn)))) ∧
        (run (Blocks.prog B) s detTape t).work ≤ s.work + d * lkW ch S.card m δ + 2 := by sorry

end DetANN.HPIM.PP
