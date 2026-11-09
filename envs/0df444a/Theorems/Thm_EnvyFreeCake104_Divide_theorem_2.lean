-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_theorem_2
-- name    : EnvyFreeCake104.Divide.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:26.161307+00:00
-- url     : https://prove2.me/theorems/08494ef8-47fe-41e1-8c61-81be51e4e484
-- title:
--   Theorem 2: Divide returns a complete envy-free allocation with at most $2\cdot 32^n n^7 (n!)^2$ queries
-- statement:
--   For a set $N$ of $n\ge1$ agents and a cake $C$, under every resolution of the protocol's free choices, Divide$(N,C)$ terminates and returns a complete envy-free allocation of $C$, using at most
--   $$2\cdot 32^n n^7 (n!)^2\ \in\ 2^{O(n\log n)}$$
--   Robertson–Webb queries. The statement has three parts:
--
--   1. for any agents $N\ne\emptyset$, any nonnegative integrable valuations, any well-formed cake $C$ and any record state valid for $N$ in which $C$ is aligned, and every choice oracle, there is fuel for which Divide$(N,C)$ succeeds and returns pairwise disjoint bundles inside $C$ whose union is $C$, envy-free among $N$, with at most $2\cdot32^n n^7(n!)^2$ queries;
--   2. in particular, for agents $\{0,\dots,n-1\}$ with densities normalized to $\int_0^1 v_i=1$, the top-level run on the cake $[0,1]$ from the initial records returns a complete envy-free allocation of $[0,1]$ with at most $2\cdot32^n n^7(n!)^2$ queries;
--   3. there is a constant $c$ with $2\cdot32^m m^7 (m!)^2\le 2^{c\,m\log_2 m}$ for every $m\ge2$.
--
--   This is the paper's main result: a bounded envy-free cake-cutting protocol for any number of agents, with a bound depending only on $n$.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: the protocol's free choices (cutter c, Line 7 tuple, dominated group, round-robin order and tie-breaks, Cut-and-Choose roles and tie-break, Permute's enumeration order) are made arbitrarily → every free choice is resolved by an arbitrary choice oracle (a function of the transcript so far), quantified universally; a step with no admissible option fails; reason: the source's protocol is correct for every resolution of its choices; a universal quantifier over adaptive oracles covers each resolution
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: Divide/Dominate terminate (while loops and recursion) → loops and recursion take a fuel argument and fail when it runs out; the statement asserts that some fuel makes the run succeed; reason: fuel is consumed only when another iteration starts, so a successful run is the source's unbounded run; ∃ fuel after ∀ oracle states termination
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
--   - generalization: Theorem 2 for the cake [0,1] with normalized valuations (§1), applied by induction to residues (p.5) → part (1) holds for every well-formed cake, unnormalized valuations and every valid aligned record state; part (2) is the [0,1] instance; reason: the proof on p.5 applies the theorem to the recursive call Divide(E, R) on a finite union of intervals; part (2) specializes part (1) to the initial records, which are valid exactly when the densities are normalized
--   - encoding: 2·32ⁿn⁷(n!)² ∈ 2^{O(n log n)} → ∃ c, ∀ m ≥ 2, 2·32^m m^7 (m!)² ≤ 2^{c·m·log₂ m}; reason: the definition of the O-class, made explicit; stated beside the explicit bound, not in its place
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.5, Theorem 2

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Theorem 2 (p.5). For a set `N` of `n ≥ 1` agents and a cake `C`, under every resolution of
the protocol's free choices, `Divide(N, C)` terminates and returns a complete envy-free
allocation of `C` using at most `2·32ⁿn⁷(n!)²` Robertson–Webb queries; and
`2·32ⁿn⁷(n!)² ∈ 2^{O(n log n)}`.

Part (1) is the statement for an arbitrary cake (a finite union of disjoint intervals, any
nonnegative integrable densities, any record state satisfying the §1.3 invariant). Part (2) is
its instance for the top-level call: agents `Fin n`, cake `[0,1]`, densities normalized to
`∫₀¹ v_i = 1`, initial records. Part (3) is the `2^{O(n log n)}` clause. -/
theorem theorem_2 :
    (∀ {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι), N.Nonempty →
      ∀ C : Piece, C.WF → ∀ s : Rec ι, s.Valid V N → s.Aligned C → ∀ o : ChoiceOracle ι,
      ∃ (fuel : ℕ) (A : ι → Piece) (s' : Rec ι) (tr : List (Event ι)),
        exec V o (divide fuel N C) s = some (A, s', tr) ∧
        IsPartialAlloc N C.toSet (fun i => (A i).toSet) ∧
        IsComplete N C.toSet (fun i => (A i).toSet) ∧
        EnvyFree V N (fun i => (A i).toSet) ∧
        queryCount tr ≤ 2 * 32 ^ N.card * N.card ^ 7 * (N.card.factorial) ^ 2) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (V : Fin n → Valuation), (∀ i, (V i).value (Set.Icc 0 1) = 1) →
      ∀ o : ChoiceOracle (Fin n),
      ∃ (fuel : ℕ) (A : Fin n → Piece) (tr : List (Event (Fin n))),
        runDivide V o fuel = some (A, tr) ∧
        IsPartialAlloc Finset.univ (Set.Icc 0 1) (fun i => (A i).toSet) ∧
        IsComplete Finset.univ (Set.Icc 0 1) (fun i => (A i).toSet) ∧
        EnvyFree V Finset.univ (fun i => (A i).toSet) ∧
        queryCount tr ≤ 2 * 32 ^ n * n ^ 7 * (n.factorial) ^ 2) ∧
    (∃ c : ℝ, ∀ m : ℕ, 2 ≤ m →
      ((2 * 32 ^ m * m ^ 7 * (m.factorial) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (c * m * Real.logb 2 m)) := by sorry

end EnvyFreeCake104.Divide
