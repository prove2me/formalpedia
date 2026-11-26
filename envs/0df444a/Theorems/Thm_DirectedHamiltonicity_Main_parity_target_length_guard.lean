-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_parity_target_length_guard
-- name    : DirectedHamiltonicity.Main.parity_target_length_guard
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:23:24.907881+00:00
-- url     : https://prove2.me/theorems/2f63af0e-eb73-4760-ac8c-e1c8c8f5ec76
-- title:
--   Proposition 4: a uniform RAM guard for the unbounded final integer
-- statement:
--   Consider the official weighted parity input with arbitrary signed target $B$, $n$ vertices, $m$ arcs, and weights at most $W$. Let $L$ be the number of tape bits preceding the encoding of $B$. One fixed log-cost RAM, from its initial state and for every coin string, reports whether $B<0$ or the binary magnitude has more than $2L$ bits. Its cost is at most $10000(L+200)^3$, with $L\le 21(n+m+W+1)^2$. Every rejected instance has zero Hamiltonian paths of weight $B$. On the other branch the target is nonnegative and has width at most $2L$. The bound is independent of the binary length of $B$.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission #811. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf Proposition 4, PDF p.5, and the registered encoding DirectedHamiltonicity.Main.encodeParityInstance. Implementation lemma for the unrestricted target in the formal statement.

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms

open TargetedSamplers DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph

open Classical in
theorem DirectedHamiltonicity.Main.parity_target_length_guard :
    ∃ P : TargetedSamplers.Program, ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ),
      (∀ e, w e ≤ W) → ∀ (s t : Fin n) (B : ℤ) (coins : List Bool),
        let L := (encodeParityInstance n m tail head w s t 0).length - 2
        let flag := decide (B<0 ∨ 2*L < B.natAbs.size)
        L ≤ 21*(n+m+W+1)^2 ∧
        P.RunsIn (runTapes (encodeParityInstance n m tail head w s t B) coins)
          (10000*(L+200)^3) (some [flag]) ∧
        (flag = true → Multidigraph.weightedPathCount
          (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t B = 0) ∧
        (flag = false → 0 ≤ B ∧ B.natAbs.size ≤ 2*L) := by sorry
