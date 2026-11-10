-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_5_5
-- name    : ChengCapClustering.Soft.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:21.262179+00:00
-- url     : https://prove2.me/theorems/24b02f6e-383d-4644-b049-a90e90e86415
-- title:
--   Lemma 5.5 — candidate centers $\Gamma\supseteq P$ of size $\le n^{N+3}\lceil\log_2(4n)\rceil$, $O(Nd)$ steps per point, $(1+\eta)$-optimal for every nonempty $Q\subseteq P$
-- statement:
--   Let $P$ be a multiset of $n\ge2$ points of $\mathbb R^d$, $z\ge1$ and $\eta\in(0,1]$, and let $N=\lceil(z4^z/\eta)^2\rceil$. One can compute a set $\Gamma\subset\mathbb R^d$ that contains the points of $P$, with $|\Gamma|\le n^{N+3}\lceil\log_2(4n)\rceil$, using $O(Nd)$ arithmetic operations, square roots and real powers per point of $\Gamma$, such that $\min_{c\in\Gamma}\Psi_Q(c)\le(1+\eta)\min_{c\in\mathbb R^d}\Psi_Q(c)$ for every nonempty multiset $Q\subseteq P$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: using O(Nd) arithmetic operations, square roots and real powers per point of Γ → one program (z, η read from the input) and one absolute constant C: the run halts within C · N · (d+1) · |G| steps, |G| the number of distinct output points; reason: total work of O(Nd) per output point; d + 1 avoids the degenerate d = 0
--   - encoding: a set Γ ⊂ ℝ^d with |Γ| ≤ n^{N+3}⌈log₂(4n)⌉; nonempty multisets Q ⊆ P → a duplicate-free output list G whose length is the cardinality of Γ; nonempty sets of client indices Q; reason: listing a finite set without repetitions preserves both its size and the per-distinct-candidate running-time bound; sub-multisets of P are sets of client indices
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 5.5, printed p. 29 / PDF p. 31

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering

namespace ChengCapClustering.Soft

/-- Lemma 5.5 (Candidate centers), printed p. 29 / PDF p. 31. For a multiset `P` of `n ≥ 2` points
of `ℝ^d`, `z ≥ 1`, `η ∈ (0, 1]` and `N = ⌈(z 4^z / η)^2⌉`, one program computes a duplicate-free list `Γ` of points
of `ℝ^d` that contains the points of `P`, has at most `n^{N+3} ⌈log₂(4n)⌉` entries, is produced with
`O(N d)` machine steps (arithmetic operations, square roots and real powers) per entry, and
satisfies `min_{c ∈ Γ} Ψ_Q(c) ≤ (1 + η) min_{c ∈ ℝ^d} Ψ_Q(c)` for every nonempty multiset `Q ⊆ P`. -/
theorem lemma_5_5 :
    ∃ prog : Program, Admissible prog ∧ ∃ C : ℝ,
      ∀ (z η : ℝ) (d n : ℕ) (p : Fin n → Euc d), 1 ≤ z → 0 < η → η ≤ 1 → 2 ≤ n →
        let N : ℕ := ⌈(z * (4 : ℝ) ^ z / η) ^ 2⌉₊
        ∃ (t : ℕ) (G : List (Euc d)),
          (run prog (initState [(n : ℤ), (d : ℤ)] ([z, η] ++ coordList p)) t).halted = true ∧
          (t : ℝ) ≤ C * (N : ℝ) * ((d + 1 : ℕ) : ℝ) * (G.length : ℝ) ∧
          G.Nodup ∧
          (∀ i, p i ∈ G) ∧
          G.length ≤ n ^ (N + 3) * ⌈Real.logb 2 (4 * (n : ℝ))⌉₊ ∧
          (∀ Q : Finset (Fin n), Q.Nonempty →
            ∃ c ∈ G, psi z Q p c ≤ (1 + η) * ⨅ c' : Euc d, psi z Q p c') ∧
          OutputIs (run prog (initState [(n : ℤ), (d : ℤ)] ([z, η] ++ coordList p)) t)
            [(G.length : ℤ)] (coordList fun j : Fin G.length => G.get j) := by sorry

end ChengCapClustering.Soft
