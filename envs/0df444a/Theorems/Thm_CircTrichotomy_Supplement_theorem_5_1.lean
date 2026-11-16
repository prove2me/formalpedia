-- Prove2me | Theorems.Thm_CircTrichotomy_Supplement_theorem_5_1
-- name    : CircTrichotomy.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:16:05.321098+00:00
-- url     : https://prove2.me/theorems/f1835369-aff5-45fa-b181-9a61774c8865
-- title:
--   Theorem 5.1 — seven characterizations of sublinear circuit size for neutral letter languages
-- statement:
--   Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language with a **neutral letter** $c$: $uv\in L\iff ucv\in L$ for all $u,v\in\Sigma^*$ with $uv\ne\varepsilon$.
--
--   **Theorem 5.1.** The following are equivalent:
--
--   1. $L\in\mathrm{SizeDepth}(O(\log^2 n),O(1))$.
--   2. $L\in\mathrm{SizeDepth}(O(\log n\log\log n),O((\log\log n)^2))$.
--   3. $L\in\mathrm{Size}(o(n))$.
--   4. The syntactic semigroup $S(L)$ is in $\mathbf{MNil}$: it is a finite aperiodic monoid in which every idempotent commutes with every element.
--   5. $L$ is a union of $\mathcal C^{t,0}_1$-classes for some $t\ge1$, where $u\,\mathcal C^{t,0}_1\,v$ means that every letter occurs equally often in $u$ and $v$ up to threshold $t$, and the occurrences of the rare letters (those occurring fewer than $t$ times), together with the first and last positions, appear in the same order.
--   6. $L$ is a finite Boolean combination of disjoint monomials $\Gamma^*a_0\Gamma^*\cdots a_{n-1}\Gamma^*$ ($\Gamma\subseteq\Sigma$, $a_i\in\Sigma\setminus\Gamma$).
--   7. $L$ is definable in $\mathcal L^1[\mathcal B_{[<]},\Sigma]$: the one-variable Lindström logic with letter predicates only and the bounded quantifiers definable by quantifier-free formulas over the order $<$.
--
--   It is the neutral-letter specialization of Theorem 2.8: for neutral letter languages the modular and positional ingredients disappear, and sublinear circuit size coincides with Straubing's class $\mathbf{MNil}$.
--
--   **Formalization Note** The seven clauses are a `List.TFAE` in the paper's order. (1)–(3) use the published `InSizeDepth`/`InSize`, (4) the published `SyntSemigroup`, (5) the published `CongTD 1 t 0`, (6) the published `BoolComb` (inside $\Sigma^+$), (7) the published `L1Definable` and `BoundedDefinable` with the empty vocabulary and the single predicate $x_0<x_1$.
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L, [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular languages with those accepted by finite automata; L ⊆ Σ⁺ is [] ∉ L; the base mission's convention
--   - encoding: functions ℕ>0 → ℝ≥0, log, O(1) → functions ℕ → ℝ, Real.logb 2, BigO of the constant 1; reason: the asymptotic classes never see n = 0 and are invariant under the base of log; the published theorem_2_8's convention
--   - encoding: (4): the syntactic semigroup of L is in MNil → InMNil (SyntSemigroup L): finite, has an identity element, ∀ x ∃ k, x^(k+1) = x^(k+2), and e x = x e for every idempotent e; reason: the definition of MNil on p.40; for finite semigroups aperiodicity is equivalent to ∃ n ≥ 1, x^n = x^(n+1)
--   - encoding: (5): L is a disjoint union of 𝒞^{t,0}_1-classes for some t ∈ ℕ>0 → ∃ t > 0, for all non-empty u, v with CongTD 1 t 0 u v, u ∈ L ↔ v ∈ L; reason: a subset of Σ⁺ is a union of classes of an equivalence relation iff it is saturated; the classes are disjoint automatically; the published theorem_2_8 (5) uses the same form
--   - encoding: (6): a finite Boolean combination of disjoint monomials (languages in Σ*) → BoolComb (complements in Σ⁺) of the languages K ∩ Σ⁺, K a disjoint monomial; reason: {ε} = ∅* is a disjoint monomial, so K ∩ Σ⁺ and Σ⁺-complements are Boolean combinations in Σ*, and intersecting with Σ⁺ maps Boolean combinations in Σ* onto those in Σ⁺; same subsets of Σ⁺
--   - encoding: (7): L¹ formulas in variables x₀, …, x_{k−1}; the signature Σ → the published L1Form written in one variable x; the empty numerical vocabulary (letter predicates and equality only), quantifiers BoundedDefinable over the single predicate x₀ < x₁; reason: every subformula has at most one free variable, so renaming bound variables changes no semantics; L¹[B_[<], Σ] has no numerical predicates or constants
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 5.1, p.11 (restated p.40; proof pp.40–41); neutral letters §5, p.10 and §B.5.1, p.39; MNil p.40; Definition B.4, p.22; disjoint monomials §B.4, p.29; Definitions B.14, B.16, pp.27–28

import Mathlib
import Definitions.Def_CircTrichotomy_InSizeDepth
import Definitions.Def_CircTrichotomy_BigO
import Definitions.Def_CircTrichotomy_LittleO
import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_CongTD
import Definitions.Def_CircTrichotomy_BoolComb
import Definitions.Def_CircTrichotomy_L1Form
import Definitions.Def_CircTrichotomy_BoundedDefinable
import Definitions.Def_CircTrichotomy_Supplement_HasNeutralLetter
import Definitions.Def_CircTrichotomy_Supplement_InMNil
import Definitions.Def_CircTrichotomy_Supplement_IsDisjointMonomial

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- **Theorem 5.1** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 5.1, p.11; restated
p.40): "Let L ⊆ Σ+ be a regular neutral letter language. Then, the following statements are
equivalent:
(1) L ∈ SizeDepth(O(log² n), O(1)).
(2) L ∈ SizeDepth(O(log n log log n), O((log log n)²)).
(3) L ∈ Size(o(n)).
(4) The syntactic semigroup of L is in MNil.
(5) L is a disjoint union of 𝒞^{t,0}_1-classes for some t ∈ ℕ>0.
(6) L is a finite Boolean combination of disjoint monomials.
(7) L is definable in L¹[B_[<], Σ]."

**Formalization Note**
* The clauses are a `List.TFAE` of the seven entries, in the paper's order.
* `log` is `Real.logb 2`; `O(1)` is `O` of the constant `1` (as in the published `theorem_2_8`).
* (4): `S(L)` is the published `SyntSemigroup L`; `InMNil` asserts finiteness, an identity element,
  aperiodicity and `ex = xe` for idempotents `e`.
* (5): `𝒞^{t,0}_1` is the published `CongTD 1 t 0`; "a union of classes" is: any two non-empty
  words `u 𝒞^{t,0}_1 v` are both in `L` or both out.
* (6): Boolean combinations inside `Σ⁺` (published `BoolComb`) of the languages `K ∩ Σ⁺`, `K` a
  disjoint monomial. Since `{ε} = ∅*` is a disjoint monomial, these are exactly the subsets of `Σ⁺`
  that are Boolean combinations of disjoint monomials in `Σ*`.
* (7): published `L1Definable` with the empty numerical vocabulary (only letter predicates and
  equality: the `Σ` of `L¹[·, Σ]`) and the quantifiers `B_[<]`: `BoundedDefinable` over the
  single predicate `x₀ < x₁`. -/
theorem theorem_5_1 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) (hneutral : HasNeutralLetter L) :
    List.TFAE
      [ InSizeDepth L (fun f => BigO f (fun n => Real.logb 2 n ^ 2)) (fun g => BigO g (fun _ => 1)),
        InSizeDepth L (fun f => BigO f (fun n => Real.logb 2 n * Real.logb 2 (Real.logb 2 n)))
          (fun g => BigO g (fun n => Real.logb 2 (Real.logb 2 n) ^ 2)),
        InSize L (fun f => LittleO f (fun n => (n : ℝ))),
        InMNil (SyntSemigroup L),
        ∃ t : ℕ, 0 < t ∧ ∀ u v : List α, u ≠ [] → v ≠ [] → CongTD 1 t 0 u v → (u ∈ L ↔ v ∈ L),
        BoolComb {K | ∃ M : Language α, IsDisjointMonomial M ∧ K = {w | w ≠ [] ∧ w ∈ M}} L,
        L1Definable (⟨∅, ∅⟩ : Vocab)
          (BoundedDefinable ({⟨2, fun a => a 0 < a 1⟩} : Set (Σ r : ℕ, (Fin r → ℕ) → Prop))) L ] := by sorry

end Supplement

end CircTrichotomy
