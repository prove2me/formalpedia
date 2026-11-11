-- Prove2me | Theorems.Thm_CircTrichotomy_theorem_2_8
-- name    : CircTrichotomy.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:42.954663+00:00
-- url     : https://prove2.me/theorems/d36ca558-2230-42a3-bf17-b2f4af1961d1
-- title:
--   Theorem 2.8 — the sublinear-size characterization theorem
-- statement:
--   **Theorem 2.8** (Sublinear-Size Characterization). Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language. The following are equivalent:
--   1. $L\in\mathrm{SizeDepth}(O(\log^2 n),O(1))$.
--   2. $L\in\mathrm{SizeDepth}(O(\log n\log\log n),O((\log\log n)^2))$.
--   3. $L\in\mathrm{Size}(o(n))$, or equivalently $c(L)\in o(n)$.
--   4. The syntactic morphism of $L$ is in $\mathbf X$.
--   5. $L$ is a union of $\simeq_k$-classes for some $k\ge1$.
--   6. $L$ is a finite positive Boolean combination of finite languages and languages $uKv$ with $u,v\in\Sigma^+$ and $K$ a modular disjoint monomial or a modular threshold language.
--   7. $L$ is a finite Boolean combination of finite languages and languages $uKv$ with $u,v\in\Sigma^+$ and $K$ a modular disjoint monomial.
--   8. $L$ is definable in $\mathcal L^1[\mathcal B_{[<,+\omega]},\Sigma,<,+\omega,\mathrm{mod},\min,\max]$.
--   9. $L$ is definable in $\mathcal L^1[\mathcal B_{\mathrm{num}[O(n^2),O(1)]},\Sigma,\mathrm{arb}]$.
--   10. $L$ is definable in $\mathcal L^1[\mathcal B_{\mathrm{num}[O(n\log n),O(\log^2 n)]},\Sigma,\mathrm{arb}]$.
--
--   With Theorem 3.1 it gives the gap between $O(\log n\log\log n)$ and $\Omega(n)$ in the trichotomy, and it decides the class of a regular language from its syntactic morphism.
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: log → Real.logb 2; reason: log is base two (p.58); every asymptotic class used is invariant under the base
--   - encoding: the ω-powers in the identities (1) of X → any e, f with IsOmegaPow (idempotent positive powers); reason: in a finite semigroup (S(L) for regular L, S for a stamp) there is exactly one such element, the ω-power
--   - reading: (3): L ∈ Size(o(n)), or equivalently c(L) ∈ o(n) → two separate entries of the TFAE list: InSize L (o(n)) and LittleO c(L) n; reason: the clause asserts both forms and their equivalence; a list of eleven equivalent statements states exactly that
--   - encoding: (5): L is a union of ≃_k-classes → for all non-empty u, v with u ≃_k v, u ∈ L ↔ v ∈ L; reason: same statement for L ⊆ Σ⁺
--   - encoding: (6), (7): finite (positive) Boolean combinations → PosBoolComb / BoolComb inside Σ⁺ of finite subsets of Σ⁺ and {u x v | x ∈ K}; reason: all languages are positive (p.16); an inductive closure uses finitely many generators
--   - encoding: (8)–(10): L¹ formulas with variables x₀, …, x_{k−1} in quantifier arguments → L1Form written in one variable x, a quantifier binding x in each argument; reason: every subformula has at most one free variable; renaming bound variables changes no semantics
--   - encoding: (9), (10): num[O(f), O(g)] predicates R ⊆ ℕᵏ and circuits C_n : ({0,1}ⁿ)ᵏ → {0,1} → relations on ℕ computed by single-output (k·n)-circuits over Bool (Definition A.2), inputs bin_n most significant bit first; reason: Definition B.18 with the circuit model of Definition A.2
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.8, p.6 (restated p.33)

import Mathlib
import Definitions.Def_CircTrichotomy_circuitComplexity
import Definitions.Def_CircTrichotomy_InSizeDepth
import Definitions.Def_CircTrichotomy_BigO
import Definitions.Def_CircTrichotomy_LittleO
import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_InX
import Definitions.Def_CircTrichotomy_simeqTD
import Definitions.Def_CircTrichotomy_BoolComb
import Definitions.Def_CircTrichotomy_IsModDisjointMonomial
import Definitions.Def_CircTrichotomy_thr
import Definitions.Def_CircTrichotomy_L1Form
import Definitions.Def_CircTrichotomy_BoundedDefinable
import Definitions.Def_CircTrichotomy_NumComputable

set_option autoImplicit false

namespace CircTrichotomy

/-- **Theorem 2.8 (Sublinear-Size Characterization)** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.8, p.6; restated p.33): "Let
L ⊆ Σ⁺ be a regular language. Then the following statements are equivalent:
(1) L ∈ SizeDepth(O(log² n), O(1)).
(2) L ∈ SizeDepth(O(log n log log n), O((log log n)²)).
(3) L ∈ Size(o(n)), or equivalently c(L) ∈ o(n).
(4) The syntactic morphism of L is in X.
(5) L is a union of ≃_k-classes for some k ∈ ℕ>0.
(6) L is a finite positive Boolean combination of finite languages and languages of the form uKv,
where u, v ∈ Σ⁺ and K is either a modular disjoint monomial, or a modular threshold language.
(7) L is a finite Boolean combination of finite languages and languages of the form uKv, where
u, v ∈ Σ⁺ and K is a modular disjoint monomial.
(8) L is definable in L¹[B_{[<,+ω]}, Σ, <, +ω, mod, min, max].
(9) L is definable in L¹[B_{num[O(n²),O(1)]}, Σ, arb].
(10) L is definable in L¹[B_{num[O(n log n),O(log² n)]}, Σ, arb]."

**Formalization Note**
* The clauses are a `List.TFAE` of eleven entries: (1), (2), the two forms of (3) ("L ∈ Size(o(n))"
  and "c(L) ∈ o(n)", which the paper states are equivalent), then (4)–(10).
* `log` is `Real.logb 2`; `O(1)` is `O` of the constant `1`.
* (5): any two non-empty words `u ≃_k v` are both in `L` or both out.
* (6), (7): Boolean combinations inside `Σ⁺`; `uKv = {u x v | x ∈ K}`; a modular threshold language is
  `Thr_{i,k}(a, t)` with `k, t ≥ 1`, `i < k` (Definition B.22).
* (8)–(10): `L¹` definability (Definition B.14) with the bounded `τ`-definable quantifiers of
  Definition B.16 for `τ = <, +ω`, resp. `τ = num[O(n²), O(1)]`, `num[O(n log n), O(log² n)]`
  (Definition B.18, `n` the bit length), and the vocabularies `<, +ω, mod, min, max`, resp. `arb`. -/
theorem theorem_2_8 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) :
    List.TFAE
      [ InSizeDepth L (fun f => BigO f (fun n => Real.logb 2 n ^ 2)) (fun g => BigO g (fun _ => 1)),
        InSizeDepth L (fun f => BigO f (fun n => Real.logb 2 n * Real.logb 2 (Real.logb 2 n)))
          (fun g => BigO g (fun n => Real.logb 2 (Real.logb 2 n) ^ 2)),
        InSize L (fun f => LittleO f (fun n => (n : ℝ))),
        LittleO (fun n => (circuitComplexity L n : ℝ)) (fun n => (n : ℝ)),
        InX (syntMorphism L),
        ∃ k : ℕ, 0 < k ∧ ∀ u v : List α, u ≠ [] → v ≠ [] → simeqK k u v → (u ∈ L ↔ v ∈ L),
        PosBoolComb ({K | IsFinitePosLang K} ∪
          {K | ∃ u v : List α, u ≠ [] ∧ v ≠ [] ∧ ∃ M : Language α,
            (IsModDisjointMonomial M ∨
              ∃ k t : ℕ, 0 < k ∧ 0 < t ∧ ∃ i < k, ∃ a : α, M = thr k i a t) ∧
            K = {w | ∃ x ∈ M, w = u ++ x ++ v}}) L,
        BoolComb ({K | IsFinitePosLang K} ∪
          {K | ∃ u v : List α, u ≠ [] ∧ v ≠ [] ∧ ∃ M : Language α, IsModDisjointMonomial M ∧
            K = {w | ∃ x ∈ M, w = u ++ x ++ v}}) L,
        L1Definable ordVocab (BoundedDefinable ordRels) L,
        L1Definable arbVocab
          (BoundedDefinable (numRels (fun n => (n : ℝ) ^ 2) (fun _ => 1))) L,
        L1Definable arbVocab
          (BoundedDefinable (numRels (fun n => (n : ℝ) * Real.logb 2 n)
            (fun n => Real.logb 2 n ^ 2))) L ] := by sorry

end CircTrichotomy
