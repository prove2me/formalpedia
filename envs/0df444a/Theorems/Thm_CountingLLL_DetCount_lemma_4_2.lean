-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_4_2
-- name    : CountingLLL.DetCount.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:12.469101+00:00
-- url     : https://prove2.me/theorems/6d157730-691e-4e5c-b954-c183408624b3
-- title:
--   Lemma 4.2 — the $\mathrm{free}^{(1)}$ reduction
-- statement:
--   Let $\mathcal E$ be a family of constraints of a CSP formula $\Phi$, $c_0\in\mathcal E$ and $T\in\mathfrak T_{\mathcal E,c_0}$, and let
--   $$\mathrm{free}^{(1)}(T)=\{c\in\mathrm{free}(T):\mathrm{dist}_{G(\mathcal E)}(c,T)=1\}.$$
--   Then:
--   1. $|\mathrm{free}^{(1)}(T)|\le(D-1)|T|+1$, where $D$ is the dependency degree of $\mathcal E$;
--   2. Whenever $\mathbb P[\mathrm{free}(T)]>0$, $\mathbb P\big[\bigwedge_{c\in T}\neg c\;\big|\;\mathrm{free}(T)\big]=\mathbb P\big[\bigwedge_{c\in T}\neg c\;\big|\;\mathrm{free}^{(1)}(T)\big]$;
--   3. $\mathrm{free}^{(1)}(T)$ can be constructed with $\mathrm{poly}(k,q,D,|T|)$ graph operations. Precisely, one fixed program using only word access, index addition/subtraction, comparisons and control (no multiplication, division, remainder or oracle queries), run on the shared dependency lists of $G(\mathcal C)$ together with a membership array of $\mathcal E$ and the list of $T$, halts with a list in memory whose entries are exactly the elements of $\mathrm{free}^{(1)}(T)$. It executes at most $(k\,q\,D\,|T|+2)^C$ instructions, with $k,q,D$ the parameters of $\Phi$ and $C$ an absolute constant.
--
--   It makes the coefficients of the expansion computable from a neighbourhood of $T$ of size $O(D|T|)$.
--
--   Differences from the source:
--   - generalization: T ∈ 𝔗_{C,c₀} for the formula’s constraint set C → T ∈ 𝔗_{E,c₀} for every constraint family E; the cardinality bound uses the degree of E, the operation count the parameters k, q, D of Φ; reason: E = all constraints is the source statement; the proof of Lemma 4.1 applies the lemma to subfamilies with the shared dependency lists (PDF 13)
--   - reading: poly(k, q, D, |T|) graph operations → at most (k·q·D·|T| + 2)^C executed instructions of an IsGraphProgram, one absolute C, on the explicit layout of shared neighbour lists of G(C), a membership array for E and the list of T; reason: only word loads/stores, index addition/subtraction, comparisons and control are admitted; multiplication, division, remainder and oracle queries are excluded; the +2 keeps the base at least 2
--   - encoding: free^{(1)}(T) can be constructed → the program halts with output (address, length) of a memory list that is a permutation of the sorted list of free^{(1)}(T); reason: the constructed set is written out explicitly
--   - encoding: P[⋀ ¬c | free(T)] = P[⋀ ¬c | free^{(1)}(T)] → the identity under 0 < P[free(T)]; reason: the conditional probability is defined only then; it holds under Condition 1.1 by Theorem 2.1
--   - encoding: a constraint set C (vertex set of G(C)) → a subfamily E of the constraint indices Fin m of a formula Φ; G(E) lives on Fin m with the constraints outside E isolated; reason: every constraint set is the full family of some formula; walks between members of E stay inside E
--   - encoding: an arbitrary fixed ordering of the constraints (lowest index in Algorithm 1) → the order of the index type Fin m; reason: the index order is an arbitrary fixed ordering; every ordering arises by relabelling the constraints
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - generalization: the formula satisfies Condition 1.1 and the standing assumptions in the surrounding section → the cardinality and construction clauses hold for every CSP; the probability identity assumes only P[free(T)] > 0; reason: the graph arguments use no probability assumption; separation of the variable sets proves the identity whenever its conditioning event has positive probability, which Theorem 2.1 supplies for every source instance
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 4.2, PDF p. 13 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Machine

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 4.2, for a constraint family `E` of `Φ`, `c₀ ∈ E` and `T ∈ 𝔗_{E,c₀}`, with
`free^{(1)}(T) = {c ∈ free(T) : dist_{G(E)}(c, T) = 1}`:
1. `|free^{(1)}(T)| ≤ (D − 1)|T| + 1`, `D` the dependency degree of `E`;
2. `P[⋀_{c∈T} ¬c | free(T)] = P[⋀_{c∈T} ¬c | free^{(1)}(T)]` (whenever `P[free(T)] > 0`, i.e.
   whenever the left side is defined);
3. one fixed program in the `IsGraphProgram` fragment (word access, index addition/subtraction,
   comparisons and control; no multiplication, division, remainder or oracle queries), run on
   the shared dependency lists of `G(C)`, a membership array for `E`
   and the list of `T` (`graphWords`), outputs `free^{(1)}(T)` (address and length of a list in
   memory) after at most `(k·q·D·|T| + 2)^C` executed instructions (graph operations), with
   `k, q, D` the parameters of `Φ` and `C` an absolute constant. -/
theorem lemma_4_2 :
    (∀ (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m), c₀ ∈ E → ∀ T ∈ Φ.twoTrees E c₀,
      ((Φ.free1 E c₀ T).card : ℤ) ≤ ((Φ.Dsub E : ℤ) - 1) * T.card + 1 ∧
      (0 < Φ.prob (Φ.SatAll (Φ.free E c₀ T)) →
        Φ.treeCoeff E c₀ T = Φ.condProb (Φ.ViolAll T) (Φ.SatAll (Φ.free1 E c₀ T)))) ∧
    ∃ P : Program, ∃ C : ℕ, IsGraphProgram P ∧
      ∀ (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m), c₀ ∈ E → ∀ T ∈ Φ.twoTrees E c₀,
        ∃ t : ℕ, ∃ a len : ℤ,
          (run Φ P (initState (listMem (graphWords Φ E c₀ T)) (fun _ => 0)) t).out =
            some (a, len) ∧ 0 ≤ len ∧
          (readList (run Φ P (initState (listMem (graphWords Φ E c₀ T)) (fun _ => 0)) t).mem
              a len.toNat).Perm
            (((Φ.free1 E c₀ T).sort (· ≤ ·)).map (fun c => (c.val : ℤ))) ∧
          (run Φ P (initState (listMem (graphWords Φ E c₀ T)) (fun _ => 0)) t).steps ≤
            (Φ.kmax * Φ.qmax * Φ.Dmax * T.card + 2) ^ C := by sorry

end CountingLLL.DetCount
