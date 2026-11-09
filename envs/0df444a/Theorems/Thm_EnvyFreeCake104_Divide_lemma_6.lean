-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_lemma_6
-- name    : EnvyFreeCake104.Divide.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:13.269846+00:00
-- url     : https://prove2.me/theorems/d0bc930f-c16f-4335-ae11-af8796226afb
-- title:
--   Lemma 6: Permute returns an envy-free suffix allocation
-- statement:
--   Let $N$ be a nonempty set of $n$ agents and $(P_i)_{i\in N}$ pairwise disjoint pieces (some possibly empty). For every valid record state in which the pieces are aligned and every choice oracle, Permute$(N,(P_i))$ terminates and returns an envy-free allocation $Y$ with residue
--   $$R=\Bigl(\bigcup_{i\in N}P_i\Bigr)\setminus\Bigl(\bigcup_{i\in N}Y_i\Bigr),$$
--   and there is a bijection $\pi$ of $N$ such that every $Y_i$ is a suffix of $P_{\pi(i)}$ and:
--
--   1. some agent $i^*$ receives her piece $P_{\pi(i^*)}$ whole;
--   2. for every nonempty $S\subseteq N$ with $Y_i\ne P_{\pi(i)}$ for all $i\in S$, there are $i^*\in S$ and $j^*\in N\setminus S$ with $V_{j^*}(Y_{i^*})=V_{j^*}(Y_{j^*})$;
--   3. Permute makes at most $\binom n2 (n!)^2$ prefix cuts.
--
--   Lemma 6 is the interface of the brute-force search used by both Core and Repair.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: the protocol's free choices (cutter c, Line 7 tuple, dominated group, round-robin order and tie-breaks, Cut-and-Choose roles and tie-break, Permute's enumeration order) are made arbitrarily → every free choice is resolved by an arbitrary choice oracle (a function of the transcript so far), quantified universally; a step with no admissible option fails; reason: the source's protocol is correct for every resolution of its choices; a universal quantifier over adaptive oracles covers each resolution
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
--   - reading: a set N of n agents → N.Nonempty; reason: property (i) names an agent; the paper's agent sets are nonempty, and Permute is only called with n ≥ 2
--   - encoding: Permute makes at most C(n,2)(n!)² prefix cuts → the prefix-cut counter of the record state grows by at most C(n,2)(n!)²; reason: the counter is incremented exactly once per prefix cut
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Lemma 6 (p.10, restated p.13). For a nonempty set `N` of `n` agents and `n` pairwise
disjoint pieces `(P_i)_{i ∈ N}`, Permute returns a partial envy-free allocation `Y` of
`⋃ P_i` with residue `R`, in which, for some bijection `π` of `N`, every `Y_i` is a suffix
of `P_{π(i)}`; (i) some agent receives `P_{π(i*)}` whole; (ii) for every nonempty `S ⊆ N` of
agents none of whom receives her piece whole, some `i* ∈ S` and `j* ∉ S` have
`V_{j*}(Y_{i*}) = V_{j*}(Y_{j*})`; and Permute makes at most `C(n,2)·(n!)²` prefix cuts. -/
theorem lemma_6 {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i)) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (permute N P) s = some ((Y, R), s', tr) ∧
      EnvyFree V N (fun i => (Y i).toSet) ∧
      R.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (Y i).toSet ∧
      (∃ π : ι → ι, Set.BijOn π (N : Set ι) (N : Set ι) ∧
        (∀ i ∈ N, IsSuffix (Y i).toSet (P (π i))) ∧
        (∃ istar ∈ N, (Y istar).toSet = (P (π istar)).toSet) ∧
        (∀ S ⊆ N, S.Nonempty → (∀ i ∈ S, (Y i).toSet ≠ (P (π i)).toSet) →
          ∃ istar ∈ S, ∃ jstar ∈ N, jstar ∉ S ∧
            (V jstar).value (Y istar).toSet = (V jstar).value (Y jstar).toSet)) ∧
      s'.prefixCuts ≤ s.prefixCuts + N.card.choose 2 * (N.card.factorial) ^ 2 := by sorry

end EnvyFreeCake104.Divide
