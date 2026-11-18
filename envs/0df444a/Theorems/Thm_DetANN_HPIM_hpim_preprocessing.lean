-- Prove2me | Theorems.Thm_DetANN_HPIM_hpim_preprocessing
-- name    : DetANN.HPIM.hpim_preprocessing
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:37:05.95442+00:00
-- url     : https://prove2.me/theorems/a1c02e1f-d0fe-4c6a-82c4-6bda61a7f1f5
-- title:
--   The preprocessing program for HPIM trees
-- statement:
--   There are a deterministic PNormReg program $P$ and constants $C>1$ and $K,C'\in\mathbb N$ such that the following holds. Let $m,N\ge1$, let $Y_1,\dots,Y_N\in\mathbb R^m$ be distinct and $\delta\in(0,1/2)$. On the input state for $(Y,\delta)$ (definition `DetANN_DataStructure`), $P$ halts with $I[1]=m$ and the tree $\mathrm{hpimTree}(Y,\delta)$ stored from $I[2]$ (definition `DetANN_HPIMLayout`). Its work is at most
--   $$C'(N+m)^K(C/\delta)^{Km}\log^K(N/\delta),$$
--   and it writes at most $C'N(C/\delta)^{Km}\log^K(N/\delta)$ cells.
--
--   These are the preprocessing time and space bounds of `DetANN.lemma_3_3`. The program computes the median thresholds exactly (via a minimum spanning tree), the ladders, the certified BSPs with their centroid balancing, and the layout.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMTree

namespace DetANN.HPIM

/-- **The preprocessing program.** One deterministic PNormReg program, on input `(Y, δ)` with `m ≥ 1`,
`N ≥ 1` distinct points and `δ ∈ (0, 1/2)`, halts with `I[1] = m` and the tree `hpimTree Y δ` stored
from `I[2]` in the layout of `DetANN_HPIMLayout`, within the time and space bounds of `lemma_3_3`:
work `C' (N + m)^K (C/δ)^{Km} log^K(N/δ)` and `C' N (C/δ)^{Km} log^K(N/δ)` cells written. -/
theorem hpim_preprocessing :
    ∃ Pre : PNormReg.Program, DetProgram Pre ∧ ∃ C : ℝ, 1 < C ∧ ∃ K C' : ℕ,
      ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
        ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
          ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ t : ℕ,
            (PNormReg.run Pre (inputState Y δ) detTape t).halted = true ∧
            ((PNormReg.run Pre (inputState Y δ) detTape t).work : ℝ) ≤
              (C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K ∧
            ((cellsWritten Pre (inputState Y δ) t).card : ℝ) ≤
              (C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K ∧
            (PNormReg.run Pre (inputState Y δ) detTape t).integerMemory 1 = m ∧
            HTreeAt m (PNormReg.run Pre (inputState Y δ) detTape t)
              ((PNormReg.run Pre (inputState Y δ) detTape t).integerMemory 2) (hpimTree Y δ) := by sorry

end DetANN.HPIM
