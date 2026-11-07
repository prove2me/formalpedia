-- Prove2me | Theorems.Thm_FewInnerTSP_theorem_4_1
-- name    : FewInnerTSP.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:34:35.465614+00:00
-- url     : https://prove2.me/theorems/0a538527-bfbb-4aa4-a8cf-4d8d5a136d58
-- title:
--   Theorem 4.1 (Mixed separator and choice family)
-- statement:
--   Let $P$ be $n\ge3$ points in general position and $\Gamma$ a convex skeleton on $m\le N_0$ of them. A recursive vertex set is $V=A\sqcup H$ with $A$ off the skeleton, $H$ on it, $a=|A|\ge1$ and $|V|\le N_0$; $Q\subseteq V$ is the set to balance. Suppose $|Q|$ exceeds a fixed constant $q_0$. There are constants $C,d,q_0$ and one admissible real-RAM program, fixed before the input, which on the input (the points of $V$ with flags for $A$ and $Q$, and the positions of the skeleton vertices) halts and outputs an axis-aligned square $\sigma$ and an explicitly enumerated family $\mathcal C(\sigma)$ of edge sets such that:
--
--   1. $\sigma$ is $16/17$-balanced for $Q$: at most $16|Q|/17$ points of $Q$ inside and at most $16|Q|/17$ outside;
--   2. (i) for every packing-compliant set $F$ of allowed free edges (distinct endpoints in $V$, one in $A$) and every set $K$ of skeleton edges with endpoints in $V$, the endpoint-straddling edges of $F\cup K$ form a member of $\mathcal C(\sigma)$;
--   3. (ii) each member has at most $C\sqrt a+C$ edges;
--   4. (iii) the number of members and the running time are at most
--   $$(N_0+2)^{d}\,2^{C(\sqrt a+\log^2(N_0+2))};$$
--   5. degree restrictions, allowed-edge restrictions and mandatory crossing edges can be imposed by rejecting candidates: for every restriction, the members satisfying it still contain the straddling set of every witness of (i) satisfying it.
--
--   The construction is independent of the unknown edge set: the program and its output come before the witness.
--
--   **Formalization Note** The output is the center and balancing side $u$ of $\sigma$ and the parameter $t$ ($\sigma$ has side $tu$), then the family as lists of edge codes.
--
--   Differences from the source:
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - encoding: one can construct σ and an explicitly enumerable family, with size and total enumeration time N0^{O(1)} 2^{O(√a+log²(N0+2))} → an admissible program, fixed before the input, outputs σ and the family as edge codes; family size and (T+1) ≤ (N₀+2)^d 2^{C(√a + log²(N₀+2))}; reason: a machine statement needs an output layout; (N₀+2) as the base differs from N₀ only for N₀ ≤ 1
--   - encoding: |Q| exceeds a fixed constant; constants depend only on the fixed packing constants → q₀ < |Q| with C, d, q₀ fixed before every input; reason: the quantifier order of a uniform constant
--   - generalization: V = A ⊔ H with A ⊆ I and H ⊆ H₀, on the fixed reduced skeleton Γ of §3 (§4, p.5) → V = A ⊔ H listed without repetition, H on Γ, A off Γ, |V| ≤ N₀, for any convex skeleton Γ with m ≤ N₀ vertices of any general-position P; reason: the proof uses only the skeleton's convexity and the packing of the edges; it specializes to A ⊆ I, H ⊆ H₀ and the reduced skeleton
--   - encoding: 16/17-balanced for Q → 17 · #(Q inside the closed σ) ≤ 16|Q| and 17 · #(Q outside) ≤ 16|Q|; reason: integer form; both sides as the page defines balance (p.5)
--   - encoding: rejecting candidates loses no witness satisfying the restrictions → for every predicate R, the members satisfying R contain the straddling set of every witness of (i) whose straddling set satisfies R; reason: the page's sentence, stated for every restriction; it follows from (i)
--   - reading: packing-compliant: 'the preceding square packing bounds with the fixed universal constants' (Definition 3.4; two forms and their rescalings, constants unnamed) → IsPackingCompliant: Lemma F.1's one bound with p₀ = 32768, on closed squares; reason: Appendices B.4 and F derive every cap from this single form through constant covers; this class contains the page's, so the clause for every compliant witness is at least as strong
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 4.1, p.6 (PDF p.8); proof App. B.4, p.18 (PDF p.20) and App. F, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_FewInnerTSP_CrossingChoices
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FewInnerTSP_Layouts

namespace FewInnerTSP

open Classical in
/-- **Theorem 4.1 (Mixed separator and choice family).** Li, Ma, Gong, *Exact Euclidean TSP with Few
Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 4.1,
p.6 (PDF p.8), proof App. B.4, p.18 (PDF p.20) and App. F, p.22 (PDF p.24): "Suppose a ≥ 1 and |Q| exceeds
a fixed constant. One can construct an axis-aligned square σ that is 16/17-balanced for Q, together with an
explicitly enumerable family C(σ), such that: (i) every packing-compliant free-edge set, together with any
allowed subset of the fixed skeleton, has its endpoint-straddling edge set in C(σ); (ii) each enumerated
candidate has at most C√a + C edges; (iii) the family has size and total enumeration time at most
N0^{O(1)} 2^{O(√a+log²(N0+2))}. (6) The construction is independent of the unknown edge set. Its constants
depend only on the fixed packing constants. Degree restrictions, allowed-edge restrictions, and mandatory
crossing edges can be imposed by rejecting candidates, without losing any witness satisfying those
restrictions."

Fix general-position points `P` (`n ≥ 3`) and a convex skeleton `Γ` on `m ≤ N₀` of them. A recursive
vertex set is `V = A ⊔ H` with `A` off the skeleton, `H` on it, `a = |A| ≥ 1`, `|V| ≤ N₀`, listed by `vs`,
and `Q ⊆ V` with `|Q| > q₀`. There are constants `C, d, q₀` and one admissible program, fixed before the
input, that on `sepLayout` (`N₀, |V|, m, a`, the points of `vs` with the flags of `A` and `Q`, the list
positions of the skeleton vertices) halt and output a separator `σ` (center, balancing side `u`,
parameter `t`; `σ` is the closed square of side `t u`) followed by a list of candidates, each a list of edge
codes, decoding to edge sets `fam`, such that:
* `σ` is `16/17`-balanced for `Q`: at most `16|Q|/17` points of `Q` inside and at most `16|Q|/17` outside;
* (i) for every packing-compliant set `F` of allowed free edges (distinct endpoints in `V`, one in `A`) and
  every set `K` of skeleton edges with both endpoints in `V`, the endpoint-straddling edges of
  `F ∪ K` (with their identities) form a member of `fam`;
* (ii) every member of `fam` has at most `C √a + C` edges;
* (iii) the number of candidates and the running time are at most `(N₀ + 2)^d 2^{C(√a + log²(N₀+2))}`;
* rejection: for every restriction `R` on edge sets, the members of `fam` satisfying `R` still contain the
  straddling set of every witness of (i) whose straddling set satisfies `R`.

**Formalization Note** "Independent of the unknown edge set" is the quantifier order: the program and its
output come before the witness `(F, K)`. The rejection clause is a consequence of (i) and is stated for
completeness. `(N₀ + 2)` replaces `N₀` as the base of the polynomial factor, which differs only for
`N₀ ≤ 1`. Edge code `(0, i, j)` is the free edge between `vs[i]` and `vs[j]`, `(1, j, 0)` the skeleton edge
`j`. -/
theorem theorem_4_1 :
    ∃ (C : ℝ) (d q0 : ℕ), 0 < C ∧ ∃ Prog : MatMulTimeLP.Program, Admissible Prog ∧
      ∀ (n m : ℕ), 3 ≤ n → ∀ (P : Fin n → Pt), GeneralPos P → ∀ (Γ : Skeleton n m),
      IsConvexSkeleton P Γ → ∀ (N0 : ℕ) (vs : List (Fin n)) (A H Q : Finset (Fin n)),
      vs.Nodup → vs.toFinset = A ∪ H → Disjoint A H →
      (∀ v ∈ H, ∃ j, Γ.vert j = v) → (∀ v ∈ A, ∀ j, Γ.vert j ≠ v) →
      1 ≤ A.card → vs.length ≤ N0 → m ≤ N0 → Q ⊆ A ∪ H → q0 < Q.card →
      ∀ ω : MatMulTimeLP.Tape, ∃ (T : ℕ) (σ : SepChoice) (L : List (List EdgeCode))
        (fam : List (Finset (Edge n m))),
        MatMulTimeLP.HaltsAt Prog (sepLayout P Γ N0 vs A Q) ω T ∧
        OutputIs Prog (sepLayout P Γ N0 vs A Q) ω T
          (σ.c 0 :: σ.c 1 :: σ.u :: σ.t :: encodeFamily L) ∧
        List.Forall₂ (DecodesTo vs) L fam ∧
        17 * (Q.filter fun v => P v ∈ σ.square).card ≤ 16 * Q.card ∧
        17 * (Q.filter fun v => P v ∉ σ.square).card ≤ 16 * Q.card ∧
        (∀ (F : Finset (Sym2 (Fin n))) (K : Finset (Fin m)),
          IsPackingCompliant P F →
          (∀ e ∈ F, ¬ e.IsDiag ∧ (∀ v ∈ e, v ∈ A ∪ H) ∧ ∃ v ∈ e, v ∈ A) →
          (∀ j ∈ K, ∀ v ∈ Γ.ends (Edge.skel j), v ∈ A ∪ H) →
          ((F.image Edge.free ∪ K.image Edge.skel).filter (Straddles P Γ σ)) ∈ fam) ∧
        (∀ X ∈ fam, (X.card : ℝ) ≤ C * Real.sqrt (A.card : ℝ) + C) ∧
        ((fam.length : ℝ) ≤ ((N0 : ℝ) + 2) ^ d *
            (2 : ℝ) ^ (C * (Real.sqrt (A.card : ℝ) + Real.log ((N0 : ℝ) + 2) ^ 2)) ∧
          (T : ℝ) + 1 ≤ ((N0 : ℝ) + 2) ^ d *
            (2 : ℝ) ^ (C * (Real.sqrt (A.card : ℝ) + Real.log ((N0 : ℝ) + 2) ^ 2))) ∧
        (∀ (R : Finset (Edge n m) → Prop) (F : Finset (Sym2 (Fin n))) (K : Finset (Fin m)),
          IsPackingCompliant P F →
          (∀ e ∈ F, ¬ e.IsDiag ∧ (∀ v ∈ e, v ∈ A ∪ H) ∧ ∃ v ∈ e, v ∈ A) →
          (∀ j ∈ K, ∀ v ∈ Γ.ends (Edge.skel j), v ∈ A ∪ H) →
          R ((F.image Edge.free ∪ K.image Edge.skel).filter (Straddles P Γ σ)) →
          ((F.image Edge.free ∪ K.image Edge.skel).filter (Straddles P Γ σ)) ∈
            fam.filter fun X => R X) := by sorry

end FewInnerTSP
