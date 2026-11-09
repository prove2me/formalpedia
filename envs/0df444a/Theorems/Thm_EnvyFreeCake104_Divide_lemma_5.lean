-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_lemma_5
-- name    : EnvyFreeCake104.Divide.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:27.184318+00:00
-- url     : https://prove2.me/theorems/f555ffe7-4511-464d-9e4d-cbea41c884e1
-- title:
--   Lemma 5: the choice in Line 7 of Dominate exists
-- statement:
--   Let $N$ be a set of $n\ge3$ agents, $X$ an envy-free partial allocation with residue $R$ (pairwise disjoint well-formed pieces $X_i$, disjoint from the well-formed piece $R$), $c\in N$, and let $(Y,U)$ be **any** output of Core$(c,N,R)$ (for any valid record state in which $R$ and all $X_i$ are aligned, and any choice oracle). Suppose $(X\oplus Y,U)$ has no dominated group. Then $V_i(U)>0$ for every $i\in N$, and there are $\alpha=(4n^2)^{-t}$ with $2\le t\le n+1$, agents $i^*\ne j^*$ and a permutation $\pi$ of $N$ such that
--
--   - (S1) $i^*$ does not dominate $j^*$ in $(X,R)$;
--   - (S2) $V_i(Y_{\pi(i)})\ge V_i(Y_i)-\alpha V_i(U)$ for all $i\in N$;
--   - (S3) $V_{i^*}(Y_{\pi(j^*)})\le V_{i^*}(Y_{i^*})-4n^2\alpha V_{i^*}(U)$.
--
--   This guarantees that Line 7 of Dominate can always be executed.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: the protocol's free choices (cutter c, Line 7 tuple, dominated group, round-robin order and tie-breaks, Cut-and-Choose roles and tie-break, Permute's enumeration order) are made arbitrarily → every free choice is resolved by an arbitrary choice oracle (a function of the transcript so far), quantified universally; a step with no admissible option fails; reason: the source's protocol is correct for every resolution of its choices; a universal quantifier over adaptive oracles covers each resolution
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
--   - encoding: X is an envy-free partial allocation with residue R; X ⊕ Y gives X_i ∪ Y_i → the X_i are pairwise disjoint well-formed pieces disjoint from the well-formed piece R; X ⊕ Y is the set family X_i ∪ Y_i; reason: exactly the pairs that arise as a partial allocation and its residue
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.7, Lemma 5

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Lemma 5 (p.7). Let `n ≥ 3`, `X` an envy-free partial allocation with residue `R`,
`(Y, U)` any output of `Core(c, N, R)`, and suppose `(X ⊕ Y, U)` has no dominated group.
Then `V_i(U) > 0` for every `i`, and there are `α = (4n²)^{-t}` with `2 ≤ t ≤ n+1`, agents
`i* ≠ j*` and a permutation `π` of `N` satisfying (S1)–(S3). -/
theorem lemma_5 {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (X : ι → Piece) (R : Piece) (hX : ∀ i ∈ N, (X i).WF) (hR : R.WF)
    (hXdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (X i).toSet (X j).toSet)
    (hXR : ∀ i ∈ N, Disjoint (X i).toSet R.toSet)
    (hEF : EnvyFree V N (fun i => (X i).toSet)) (c : ι) (hc : c ∈ N)
    (s : Rec ι) (hs : s.Valid V N) (hXs : ∀ i ∈ N, s.Aligned (X i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (core N c R) s = some ((Y, U), s', tr))
    (hnone : ¬ ∃ E : Finset ι,
      IsDominatedGroup V N (fun i => (X i).toSet ∪ (Y i).toSet) U.toSet E) :
    (∀ i ∈ N, 0 < (V i).value U.toSet) ∧
    ∃ t : ℕ, 2 ≤ t ∧ t ≤ N.card + 1 ∧
      ∃ istar ∈ N, ∃ jstar ∈ N, istar ≠ jstar ∧
      ∃ π : ι → ι, Set.BijOn π (N : Set ι) (N : Set ι) ∧
        -- (S1)
        ¬ Dominates V (fun i => (X i).toSet) R.toSet istar jstar ∧
        -- (S2)
        (∀ i ∈ N, (V i).value (Y i).toSet - alphaOf N.card t * (V i).value U.toSet ≤
          (V i).value (Y (π i)).toSet) ∧
        -- (S3)
        (V istar).value (Y (π jstar)).toSet ≤ (V istar).value (Y istar).toSet -
          4 * (N.card : ℝ) ^ 2 * alphaOf N.card t * (V istar).value U.toSet := by sorry

end EnvyFreeCake104.Divide
