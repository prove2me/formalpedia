-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_shrink_progress
-- name    : EnvyFreeCake104.Divide.shrink_progress
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:25:29.27936+00:00
-- url     : https://prove2.me/theorems/d2292f09-b2ad-40ae-b8bf-29e53ce3901c
-- title:
--   Lines 9–11 of Dominate: repeated Core calls shrink the cutter's residue
-- statement:
--   **The shrinking loop of Dominate.** Let $N$ be a set of $n\ge2$ agents, $i^\ast\in N$ the cutter, $\alpha\in\mathbb R$, and $U$ a well-formed piece. Let $W=(W_i)_{i\in N}$ be an envy-free partial allocation of pairwise disjoint well-formed pieces and $R'$ a well-formed piece disjoint from every $W_i$, all aligned with valid records $s$ (as is $U$). Suppose that for some $K\in\mathbb N$
--   $$V_{i^\ast}(R')\Big(1-\tfrac1n\Big)^K\le \alpha\,V_{i^\ast}(U).$$
--   Then for every fuel $\ge K$ and every choice oracle, the loop of Lines 9–11 of Dominate ("while $V_{i^\ast}(R')>\alpha V_{i^\ast}(U)$: $(F,R')\leftarrow\mathrm{Core}(i^\ast,N,R')$, $W\leftarrow W\oplus F$") terminates successfully with $(W',R'')$ such that: the records stay valid and only gain points; every $W'_i$ and $R''$ is well formed and aligned; $W_i\subseteq W'_i\subseteq W_i\cup R'$; the $W'_i$ are pairwise disjoint and $R''=R'\setminus\bigcup_iW'_i$; $W'$ is envy-free; no difference $V_i(W_i)-V_i(W_j)$ decreases; $V_{i^\ast}(R'')\le\alpha V_{i^\ast}(U)$; and at most $K\cdot n^3(n!)^2$ queries are made.
--
--   This is the paragraph *Repeated Core calls create domination* of the proof of Lemma 1: by Lemma 3 the cutter receives exactly $1/n$ of her value of the current residue, so her value of the remaining residue shrinks by a factor at least $1-\frac1n$ per call.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, proof of Lemma 1, paragraph 'Repeated Core calls create domination' (p.9), Algorithm 2 Lines 9-11

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Lines 9-11 of Dominate (p.9): repeated Core calls with cutter `i*` on the residue `R'`.
If `K` calls suffice to bring `V_{i*}(R')` below `α V_{i*}(U)` (each call keeps at most a
`(1 - 1/n)` fraction of the cutter's value of the residue), then with fuel at least `K` the
loop terminates; it keeps the allocation envy-free, only enlarges bundles with parts of `R'`,
does not decrease any difference `V_i(W_i) - V_i(W_j)`, leaves `V_{i*}(R'') ≤ α V_{i*}(U)`, and
makes at most `K` Core calls' worth of queries. -/
theorem shrink_progress {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (istar : ι) (hi : istar ∈ N) (α : ℝ) (U : Piece) (hU : U.WF) :
    ∀ (K fuel : ℕ), K ≤ fuel → ∀ (W : ι → Piece) (R' : Piece) (s : Rec ι)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      (∀ i ∈ N, (W i).WF) → R'.WF →
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W i).toSet (W j).toSet) →
      (∀ i ∈ N, Disjoint (W i).toSet R'.toSet) →
      EnvyFree V N (fun i => (W i).toSet) →
      s.Valid V N → (∀ i ∈ N, s.Aligned (W i)) → s.Aligned R' → s.Aligned U →
      (V istar).value R'.toSet * (1 - 1 / (N.card : ℝ)) ^ K ≤ α * (V istar).value U.toSet →
      ∃ (W' : ι → Piece) (R'' : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((shrink N istar α U fuel W R').run s) tr₀ =
          some (((W', R''), s'), tr) ∧
        s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (W' i).WF ∧ s'.Aligned (W' i)) ∧
        R''.WF ∧ s'.Aligned R'' ∧
        (∀ i ∈ N, (W i).toSet ⊆ (W' i).toSet ∧ (W' i).toSet ⊆ (W i).toSet ∪ R'.toSet) ∧
        (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W' i).toSet (W' j).toSet) ∧
        R''.toSet = R'.toSet \ ⋃ i ∈ N, (W' i).toSet ∧
        EnvyFree V N (fun i => (W' i).toSet) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (W i).toSet - (V i).value (W j).toSet ≤
          (V i).value (W' i).toSet - (V i).value (W' j).toSet) ∧
        (V istar).value R''.toSet ≤ α * (V istar).value U.toSet ∧
        queryCount tr ≤ queryCount tr₀ + K * (N.card ^ 3 * (N.card.factorial) ^ 2) := by sorry

end EnvyFreeCake104.Divide
