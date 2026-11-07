-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_5_3
-- name    : FewInnerTSP.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:35.712798+00:00
-- url     : https://prove2.me/theorems/2f12bf76-465f-4c02-8465-f8556355e065
-- title:
--   Lemma 5.3 (Constant core)
-- statement:
--   There is a constant $C>0$ such that for every fixed $a_0$ there is an admissible real-RAM program with the following property. Let $P$ be $n\ge3$ points in general position, $\Gamma$ a convex skeleton on $m\le N_0$ of them, and $S$ a well-formed state on $\Gamma$ with $a\le a_0$ core vertices, $|V|\le N_0$ and $b$ terminals, given as its vertices, skeleton positions and allowed edges, each edge listed once, with weights and mandatory flags. The program halts within
--   $$(N_0+2)^{C(a_0+1)}\,2^{Cb}$$
--   steps, irrespective of the number of skeleton vertices, and outputs a family of at most $2^{b-1}$ edge sets, each a feasible cover of $S$, such that for every feasible cover $C'$ of $S$ and every external matching $X$ compatible with $C'$ some returned $R$ has $w(R)\le w(C')$ and $M(R)\cup X$ connected.
--
--   This is the base case of the recursion; its output dominates every feasible cover, packing-compliant or not.
--
--   Differences from the source:
--   - reading: solved and compressed → the returned feasible covers preserve, for every compatible external matching, the minimum over all feasible covers, and number at most 2^{b−1}; reason: the page: 'The base enumerates every feasible cover before rank reduction' (p.11), and App. C.2 applies Lemma 5.2; 2^{b−1} is 1 at b = 0 in ℕ
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - encoding: N0^{O(a0)} 2^{O(b)} time for fixed a0 → (T+1) ≤ (N₀+2)^{C(a₀+1)} 2^{Cb}, C fixed before a₀, the program chosen after a₀; reason: 'for fixed a0' lets the program depend on a₀; the O-constant does not; (N₀+2) as the base
--   - generalization: a state with a ≤ a0 on the fixed reduced skeleton of §3 → a well-formed state on any convex skeleton with m ≤ N₀ vertices of any general-position P, |V| ≤ N₀; reason: App. C.2 uses only the cyclic degree equations of the skeleton; it specializes to the reduced skeleton
--   - encoding: a state as data → the state layout, with the edge list es naming each edge of E exactly once (es.length = |E|); reason: a machine statement needs a layout; a list with repeats could outrun the time bound, and a state is a set of edges
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.3, p.10 (PDF p.12); proof App. C.2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_FewInnerTSP_State
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FewInnerTSP_Layouts

namespace FewInnerTSP

/-- **Lemma 5.3 (Constant core).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.3, p.10 (PDF p.12),
proof App. C.2, p.19 (PDF p.21): "For fixed a0, a state with a ≤ a0 can be solved and compressed in
N0^{O(a0)} 2^{O(b)} time, irrespective of the number of remaining skeleton vertices."

There is `C > 0` such that for every `a₀` there is an admissible program which, for every instance
(general-position `P`, `n ≥ 3`, a convex skeleton `Γ` on `m ≤ N₀` points) and every well-formed state `S`
on `Γ` with `a ≤ a₀` core vertices and `|V| ≤ N₀`, on the input `stateLayout` (`N₀, |V|, m, a, b, |E|`, the
vertices with the flags of `A` and `B`, the skeleton positions, and each allowed edge once with its code,
weight and mandatory flag) halts within `(N₀ + 2)^{C(a₀+1)} 2^{C b}` steps and outputs a family of at most
`2^{b−1}` edge sets, each a feasible cover of `S`, such that for every feasible cover `C` of `S` (packing
compliant or not) and every external matching `X` compatible with `C` some returned `R` has
`w(R) ≤ w(C)` and is compatible with `X`.

**Formalization Note** "Solved" is read as the page's proof does: "The base enumerates every feasible
cover before rank reduction" (p.11), so the family preserves the minimum over all feasible covers, which
implies completion domination. "Compressed" is the bound `2^{b−1}` (in `ℕ`, so `1` when `b = 0`, the empty
state's one empty cover). The program may depend on `a₀` ("for fixed a0"), the constant `C` may not.
`(N₀ + 2)` replaces `N₀` as the base. `es` lists each edge of `E` exactly once (`es.length = |E|`): a list
with repeats could be longer than the time bound, and a program could not read to its end. -/
theorem lemma_5_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ a0 : ℕ, ∃ Prog : MatMulTimeLP.Program, Admissible Prog ∧
      ∀ (n m : ℕ), 3 ≤ n → ∀ (P : Fin n → Pt), GeneralPos P → ∀ (Γ : Skeleton n m),
      IsConvexSkeleton P Γ → ∀ (N0 : ℕ) (S : State n m), IsState Γ S → S.A.card ≤ a0 →
      S.V.card ≤ N0 → m ≤ N0 → ∀ (vs : List (Fin n)) (es : List EdgeCode),
      IsListing vs S.V → DecodesTo vs es S.E → es.length = S.E.card →
      ∀ ω : MatMulTimeLP.Tape, ∃ (T : ℕ) (L : List (List EdgeCode))
        (fam : List (Finset (Edge n m))),
        MatMulTimeLP.HaltsAt Prog (stateLayout P Γ N0 vs es S) ω T ∧
        (T : ℝ) + 1 ≤ ((N0 : ℝ) + 2) ^ (C * ((a0 : ℝ) + 1)) * (2 : ℝ) ^ (C * (S.B.card : ℝ)) ∧
        OutputIs Prog (stateLayout P Γ N0 vs es S) ω T (encodeFamily L) ∧
        List.Forall₂ (DecodesTo vs) L fam ∧
        fam.length ≤ 2 ^ (S.B.card - 1) ∧
        (∀ R ∈ fam, IsFeasibleCover Γ S R) ∧
        ∀ C' : Finset (Edge n m), IsFeasibleCover Γ S C' →
          ∀ X : Finset (Sym2 (Fin n)), IsPerfectMatching S.B X →
          Compatible S.B (matchingOf Γ S C') X →
          ∃ R ∈ fam, S.wtOf R ≤ S.wtOf C' ∧ Compatible S.B (matchingOf Γ S R) X := by sorry

end FewInnerTSP
