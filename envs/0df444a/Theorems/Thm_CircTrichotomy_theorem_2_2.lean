-- Prove2me | Theorems.Thm_CircTrichotomy_theorem_2_2
-- name    : CircTrichotomy.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:55.282241+00:00
-- url     : https://prove2.me/theorems/da8d74be-bff5-4e8d-bc9d-ba34169a6ccc
-- title:
--   Theorem 2.2 — the $O(1)$-characterization theorem [GM26b]
-- statement:
--   **Theorem 2.2** ([GM26b], $O(1)$-Characterization Theorem). Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language. The following are equivalent:
--   1. $c(L)\in O(1)$.
--   2. $c(L)\in o(\log n)$.
--   3. The syntactic morphism $\eta_L$ belongs to $\mathbf{QEJ_1}$: the stable semigroup $\mathrm{stab}(\eta_L)$ satisfies $epxqf=epxxqf$ and $epxyqf=epyxqf$ for all idempotents $e,f$ and all $p,q,x,y$ of $\mathrm{stab}(\eta_L)$.
--   4. $L$ is a union of $\approx_k$-classes for some $k\ge1$.
--   5. $L$ is a finite Boolean combination of finite languages and languages $u(\Gamma_0\cdots\Gamma_{k-1})^+v$ with $k\ge1$, non-empty $\Gamma_0,\dots,\Gamma_{k-1}\subseteq\Sigma$ and $u,v\in\Sigma^+$.
--   6. $L$ is definable in $\mathrm{FO}^1[\Sigma,\mathrm{arb}]$, the one-variable fragment of first-order logic with arbitrary numerical predicates.
--
--   It implies that a regular language without constant-size circuits has $c(L)\in\Omega(\log n)$, the lower bound of the almost-logarithmic case. The theorem is proved in [GM26b] (arXiv:2609.18484).
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: log → Real.logb 2; reason: log is base two (p.58); every asymptotic class used is invariant under the base
--   - encoding: (3): the stable semigroup of η_L → InQEJ1 asserts that the stability index s exists and states the identities on lenImage η_L s; reason: the stability index exists and is unique for every stamp, η_L is a stamp for regular L
--   - encoding: (4): L is a union of ≈_k-classes → for all non-empty u, v with u ≈_k v, u ∈ L ↔ v ∈ L; reason: same statement for L ⊆ Σ⁺
--   - encoding: (5): finite Boolean combination → BoolComb (inductive closure under complement in Σ⁺, binary ∩ and ∪) of finite subsets of Σ⁺ and the languages {u x v | x ∈ (Γ₀ … Γ_{k−1})⁺}; reason: all languages are positive (p.16), so complements are taken in Σ⁺; an inductive closure uses finitely many generators
--   - encoding: (6): FO¹[Σ, arb] → FO1Definable arbVocab: one-variable syntax whose numerical predicates and constants are given by their length-indexed interpretations; reason: arb is the class of all numerical predicates and constants (p.20)
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2, p.3

import Mathlib
import Definitions.Def_CircTrichotomy_circuitComplexity
import Definitions.Def_CircTrichotomy_BigO
import Definitions.Def_CircTrichotomy_LittleO
import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_InQEJ1
import Definitions.Def_CircTrichotomy_approxK
import Definitions.Def_CircTrichotomy_BoolComb
import Definitions.Def_CircTrichotomy_blockStar
import Definitions.Def_CircTrichotomy_FO1Form

set_option autoImplicit false

namespace CircTrichotomy

/-- **Theorem 2.2 ([GM26b], O(1)-Characterization Theorem)** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2, p.3; cited from
Göller, Manuel, arXiv:2609.18484): "Let L ⊆ Σ⁺ be a regular language. Then the following statements
are equivalent:
(1) c(L) ∈ O(1).
(2) c(L) ∈ o(log n).
(3) The syntactic morphism η_L belongs to the length-multiplying pseudovariety of stamps QEJ₁, i.e.,
the stable semigroup stab(η_L) of η_L satisfies the identities epxqf = epxxqf and epxyqf = epyxqf,
where e, f range over idempotents and where p, q, x, y range over all elements of stab(η_L).
(4) L is a union of ≈_k-classes for some k ∈ ℕ>0, where ≈_k denotes the following congruence on
Σ⁺: u ≈_k v if, and only if, u = v or • |u|, |v| > 2k, • u = u′xu″ and v = v′yv″ have the same
k-length prefix u′ = v′ and the same k-length suffix u″ = v″, • |x| ≡ |y| mod k, and • x and y
agree on the set of letters appearing in positions that are equivalent mod k.
(5) L is a finite Boolean combination of finite languages and languages u(Γ₀ … Γ_{k−1})⁺v, where
k ∈ ℕ>0, ∅ ≠ Γ₀, …, Γ_{k−1} ⊆ Σ and u, v ∈ Σ⁺.
(6) L is definable in FO¹[Σ, arb], more precisely in the one-variable fragment of first-order logic
with arbitrary numerical predicates."

**Formalization Note**
* The six clauses are a `List.TFAE`, in the paper's order.
* (4): "a union of ≈_k-classes" is: any two non-empty words `u ≈_k v` are both in `L` or both out.
* (5): Boolean combinations are inside `Σ⁺` (`BoolComb`, complement `Σ⁺ \ ·`); finite languages are
  finite subsets of `Σ⁺`; `u(Γ₀ … Γ_{k−1})⁺v = {u x v | x ∈ (Γ₀ … Γ_{k−1})⁺}`.
* (6): `FO¹[Σ, arb]` is `FO1Definable arbVocab`.
* `log` is `Real.logb 2`. -/
theorem theorem_2_2 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) :
    List.TFAE
      [ BigO (fun n => (circuitComplexity L n : ℝ)) (fun _ => 1),
        LittleO (fun n => (circuitComplexity L n : ℝ)) (fun n => Real.logb 2 n),
        InQEJ1 (syntMorphism L),
        ∃ k : ℕ, 0 < k ∧ ∀ u v : List α, u ≠ [] → v ≠ [] → approxK k u v → (u ∈ L ↔ v ∈ L),
        BoolComb ({K | IsFinitePosLang K} ∪
          {K | ∃ k : ℕ, 0 < k ∧ ∃ Γ : ℕ → Set α, (∀ j < k, (Γ j).Nonempty) ∧
            ∃ u v : List α, u ≠ [] ∧ v ≠ [] ∧ K = {w | ∃ x ∈ blockPlus k Γ, w = u ++ x ++ v}}) L,
        FO1Definable arbVocab L ] := by sorry

end CircTrichotomy
