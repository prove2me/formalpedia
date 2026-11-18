-- Prove2me | Theorems.Thm_EditGV897_Main_syndrome_program
-- name    : EditGV897.Main.syndrome_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:36:34.598382+00:00
-- url     : https://prove2.me/theorems/cd582a95-bb14-4ef7-a4e1-66a3d30043da
-- title:
--   Finite-program realization of the syndrome search
-- statement:
--   There is a fixed finite binary tape program and uniform natural constants $A>0,d$ that realize the prescribed exhaustive syndrome selection on the inputs of Lemma 2. For a length-$n$ affine edit family of size $M$ and a full-row-rank matrix of $b=\lceil\log_2(2M)\rceil<n$ rows satisfying the total-witness bound, the program returns the specified minimizing length-$b$ syndrome in at most
--
--   $$A(n+M+1)^d$$
--
--   actual tape transitions. Dense input parsing, exact affine-system counting, integer arithmetic, and output writing are included. This is the computational obligation for the source's syndrome search, whose candidate set has fewer than $4M$ syndromes.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §4.2, Lemma 2 and its proof, printed p.11 / PDF p.12

import Definitions.Def_EditGV897_Main_Construction
open EditGV897.Main

theorem EditGV897.Main.syndrome_program :
    ∃ (selector : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length = checkRows F.length → G.length < n →
        FullRowRank G → witnessSum F G Finset.univ ≤ 2 ^ (n - 1) →
        Runs selector (syndromeInput F G) (bitCode (chooseSyndrome F G))
          (polyBudget A d (n + F.length)) := by sorry
