-- Prove2me | Theorems.Thm_CliffordHierTest_lemma_5
-- name    : CliffordHierTest.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:03.785598+00:00
-- url     : https://prove2.me/theorems/81a0d517-5df4-4700-8110-87a655a4d3b5
-- title:
--   Lemma 5 — cocycle condition and antisymmetry of $\beta$
-- statement:
--   Let $d$ be prime and let $\beta$ be the map of Proposition 4, i.e. $W_aW_b=\tau^{\beta(a,b)}W_{a+b}$ for all $a,b\in\mathbb F_d^{2n}$. Then for all $a,b,c$:
--
--   1. (cocycle condition) $\beta(a,b+c)+\beta(b,c)=\beta(a,b)+\beta(a+b,c)$;
--   2. $\beta(a,b)-\beta(b,a)=2[a,b]$,
--
--   where for $d=2$ the term $2[a,b]$ is read as $2|[a,b]|\bmod 4$.
--
--   The cocycle identity is what makes the phases $\tau^{\beta}$ consistent, and is used in the representation-theoretic step of the main inverse theorem.
--
--   Differences from the source:
--
--   - reading: the map β given explicitly in [Hei21, §3.3.1] → every β : 𝔽_d^{2n} × 𝔽_d^{2n} → ℤ_D with W_aW_b = τ^{β(a,b)}W_{a+b} for all a, b; reason: this identity determines β uniquely (τ has order D and W_{a+b} ≠ 0), so the Lean β is the paper's map
--   - encoding: 2[a,b] (2|[a,b]| mod 4 for d = 2) → 2 · |[a,b]| cast into ZMod D; reason: equals 2[a,b] for odd d (D = d) and is the printed convention for d = 2
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.1 Lemma 5, p.4

import Mathlib
import Definitions.Def_CliffordHierTest_PauliNorm

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Lemma 5** (p.4). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For the map `β` of Proposition 4 and all `a, b, c ∈ 𝔽_d^{2n}`: the cocycle condition
`β(a, b + c) + β(b, c) = β(a, b) + β(a + b, c)` and `β(a, b) − β(b, a) = 2[a, b]`, where for
`d = 2` the term `2[a, b]` is `2|[a, b]| mod 4`.

**Formalization Note.** Stated for every `β : 𝔽_d^{2n} × 𝔽_d^{2n} → ℤ_D` satisfying the first
identity of Proposition 4; that identity determines `β` (the order of `τ` is `D` and
`W_{a+b} ≠ 0`), so this is the paper's map. `2[a, b]` is `2 · |[a, b]|` cast into
`ℤ_D = ZMod (phaseModulus d)`: for `d = 2` this is the printed `2|[a, b]| mod 4`, for odd `d`
(`D = d`) it is `2[a, b]`. -/
theorem lemma_5 (d n : ℕ) [Fact (Nat.Prime d)]
    (β : DiscretePhaseSpace d n → DiscretePhaseSpace d n → ZMod (phaseModulus d))
    (hβ : ∀ a b : DiscretePhaseSpace d n,
      cyclicWeyl d n a * cyclicWeyl d n b = weylPhase d ^ (β a b).val • cyclicWeyl d n (a + b))
    (a b c : DiscretePhaseSpace d n) :
    β a (b + c) + β b c = β a b + β (a + b) c ∧
      β a b - β b a = 2 * (((symplecticBracket a b).val : ℕ) : ZMod (phaseModulus d)) := by sorry

end CliffordHierTest
