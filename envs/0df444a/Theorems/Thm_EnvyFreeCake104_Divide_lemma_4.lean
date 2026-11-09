-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_lemma_4
-- name    : EnvyFreeCake104.Divide.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:27.63022+00:00
-- url     : https://prove2.me/theorems/fb60dfbb-6731-4130-b941-893d504e601a
-- title:
--   Lemma 4: Repair restores envy-freeness without cutting old bundles
-- statement:
--   Let $N$ be a set of $n\ge2$ agents and $0<\varepsilon\le 1/(6n^3)$. Let $D=(D_i)_{i\in N}$ be a partial allocation with residue $R$ (pairwise disjoint well-formed pieces, disjoint from the well-formed piece $R$) with $V_i(R)>0$ for all $i\in N$ and
--   $$V_i(D_i)\ge V_i(D_j)-\varepsilon V_i(R)\qquad\text{for all } i,j\in N .$$
--   Then, for every valid record state in which $R$ and all $D_i$ are aligned and every choice oracle, Repair$(N,D,R,\varepsilon)$ terminates and returns an envy-free allocation $W$ and a residue $U$ such that, for some bijection $\sigma$ of $N$ and sets $Z_j$ ($j\in N$):
--
--   1. $W_{\sigma(j)}=D_j\cup Z_j$ for every $j$;
--   2. the $Z_j\subseteq R$ are pairwise disjoint and $V_i(Z_j)\le 3n^2\varepsilon V_i(R)$ for all $i,j\in N$;
--   3. $U=R\setminus\bigcup_{j\in N}Z_j$;
--   4. the run makes at most $\dfrac n\varepsilon+n^3(n!)^2$ Robertson–Webb queries.
--
--   Repair turns an almost envy-free allocation into an exactly envy-free one while keeping every old bundle intact; Dominate uses it to keep an advantage it has created.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: the protocol's free choices (cutter c, Line 7 tuple, dominated group, round-robin order and tie-breaks, Cut-and-Choose roles and tie-break, Permute's enumeration order) are made arbitrarily → every free choice is resolved by an arbitrary choice oracle (a function of the transcript so far), quantified universally; a step with no admissible option fails; reason: the source's protocol is correct for every resolution of its choices; a universal quantifier over adaptive oracles covers each resolution
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
--   - encoding: D is a partial allocation with residue R → the D_i are pairwise disjoint well-formed pieces, each disjoint from the well-formed piece R; reason: these are exactly the pairs (D, R) that arise as a partial allocation of the cake R ∪ ⋃ D_i and its residue
--   - encoding: Repair assigns the bundles D_j ∪ Z_j, one per agent → ∃ σ bijective on N with W_{σ(j)} = D_j ∪ Z_j; reason: the paper's own reading on p.8 (W_{σ(j)} = D_j ∪ Z_j)
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 4 (restated p.11)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Lemma 4 (p.6, restated p.11). Let `n ≥ 2`, `0 < ε ≤ 1/(6n³)`, and `D` a partial
allocation with residue `R`, `V_i(R) > 0` and `V_i(D_i) ≥ V_i(D_j) - εV_i(R)` for all
`i, j`. Then Repair returns an envy-free partial allocation `W` assigning the bundles
`D_j ∪ Z_j` one per agent (`W_{σ(j)} = D_j ∪ Z_j` for a bijection `σ`), with pairwise
disjoint `Z_j ⊆ R`, `V_i(Z_j) ≤ 3n²εV_i(R)`, residue `R \ ⋃ Z_j`, and at most
`n/ε + n³(n!)²` queries. -/
theorem lemma_4 {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (6 * (N.card : ℝ) ^ 3))
    (D : ι → Piece) (R : Piece) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (hpos : ∀ i ∈ N, 0 < (V i).value R.toSet)
    (halmost : ∀ i ∈ N, ∀ j ∈ N,
      (V i).value (D j).toSet - ε * (V i).value R.toSet ≤ (V i).value (D i).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) :
    ∃ (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (repair N D R ε) s = some ((W, U), s', tr) ∧
      EnvyFree V N (fun i => (W i).toSet) ∧
      (∃ (σ : ι → ι) (Z : ι → Set ℝ), Set.BijOn σ (N : Set ι) (N : Set ι) ∧
        (∀ j ∈ N, Z j ⊆ R.toSet) ∧
        (∀ j ∈ N, ∀ k ∈ N, j ≠ k → Disjoint (Z j) (Z k)) ∧
        (∀ j ∈ N, (W (σ j)).toSet = (D j).toSet ∪ Z j) ∧
        (∀ i ∈ N, ∀ j ∈ N,
          (V i).value (Z j) ≤ 3 * (N.card : ℝ) ^ 2 * ε * (V i).value R.toSet) ∧
        U.toSet = R.toSet \ ⋃ j ∈ N, Z j) ∧
      (queryCount tr : ℝ) ≤ (N.card : ℝ) / ε + (N.card : ℝ) ^ 3 * ((N.card.factorial : ℝ)) ^ 2 := by sorry

end EnvyFreeCake104.Divide
