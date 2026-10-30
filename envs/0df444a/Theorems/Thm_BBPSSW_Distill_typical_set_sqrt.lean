-- Prove2me | Theorems.Thm_BBPSSW_Distill_typical_set_sqrt
-- name    : BBPSSW.Distill.typical_set_sqrt
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:45:42.78457+00:00
-- url     : https://prove2.me/theorems/83aae809-f2aa-433a-a5ed-c4380d0447d2
-- title:
--   Typical sets of size $2^{H+O(\sqrt n)}$ carry almost all the weight
-- statement:
--   Let $\alpha$ be a finite alphabet and $0<\varepsilon<1$. There is a constant $C$ such that for every $n$ and all probability vectors $p_1,\dots,p_n$ on $\alpha$, the product distribution $P(x)=\prod_i p_i(x_i)$ on $\alpha^n$ satisfies: there is a set $T\subseteq\alpha^n$ with
--
--   $$P(T)\ge1-\varepsilon\qquad\text{and}\qquad 2^{H-C\sqrt n}\le|T|\le2^{H+C\sqrt n},$$
--
--   where $H=\sum_iH(p_i)$ is the Shannon entropy (in bits) of $P$.
--
--   With identical $p_i$ this is the paper's statement for $P_X$ (the $\Phi/\Psi$ values of $n$ impure pairs); with $p_i$ depending on $x_i$ it is the statement for $P_{Y|X=x}$ (the $\pm$ values given the $\Phi/\Psi$ sequence $x$). It bounds the number of candidate error strings that the BXOR tests must distinguish.
--
--   Differences from the source:
--   - reading: receives almost all its weight from a set containing 2^(H+O(√n)) members → for every ε ∈ (0,1) a constant C (depending on ε and α only) and a set T of weight ≥ 1 − ε with 2^(H − C√n) ≤ |T| ≤ 2^(H + C√n); reason: standard meaning of "almost all" and of O(√n)
--   - generalization: PX i.i.d. over n-bit strings, and PY|X=x → independent components with arbitrary laws p_i on any finite alphabet; reason: covers both of the paper's distributions (identical p_i; p_i depending on x_i) with one statement
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 3, unnumbered bullet ("The probability distribution PX over n-bit strings x …")

import Mathlib
import Definitions.Def_BBPSSW_Distill_shannonBits

namespace BBPSSW.Distill

/-- **Typical sets of size `2^{H + O(√n)}`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 3 (unnumbered bullet): "The probability distribution PX over n-bit strings x, where x
represents the original sequence of Φ/Ψ values of the impure pairs, receives almost all its
weight from a set of “typical” strings containing N1 = 2^(H(X)+O(√n)) members, where H(X) is
the Shannon entropy of PX. Similarly, the conditional distribution PY|X=x of n-bit strings y,
representing the +/− values of a sequence of impure pairs whose Φ/Ψ sequence is x, receives
almost all its weight from a set of typical strings containing N2 = 2^(H(Y|X=x)+O(√n))
members."

Let `α` be a finite alphabet and `0 < ε < 1`. There is a constant `C` such that for every `n`
and all distributions `p₁, …, p_n` on `α`, the product distribution `P(x) = ∏ᵢ pᵢ(xᵢ)` on `αⁿ`
puts weight at least `1 − ε` on a set `T` with
`2^{H − C√n} ≤ |T| ≤ 2^{H + C√n}`, where `H = ∑ᵢ H(pᵢ)` is the Shannon entropy (in bits) of
`P`.

**Formalization Note.** "Almost all its weight" is weight `≥ 1 − ε` for an arbitrary
`ε ∈ (0, 1)`, and `O(√n)` is a constant `C` depending only on `ε` and `α`. The components
are independent but need not be identically distributed (a generalization): this covers
`P_X` (i.i.d. Φ/Ψ values) and `P_{Y|X=x}` (independent ± values whose law depends on `xᵢ`) at
once, with `H(P_X) = n H(p)` and `H(Y|X=x) = ∑ᵢ H(p_{xᵢ})`. -/
theorem typical_set_sqrt (α : Type*) [Fintype α] (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, ∀ (n : ℕ) (p : Fin n → α → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
      ∃ T : Finset (Fin n → α),
        1 - ε ≤ ∑ x ∈ T, ∏ i, p i (x i) ∧
        (2 : ℝ) ^ (∑ i, shannonBits (p i) - C * Real.sqrt n) ≤ (T.card : ℝ) ∧
        (T.card : ℝ) ≤ (2 : ℝ) ^ (∑ i, shannonBits (p i) + C * Real.sqrt n) := by sorry

end BBPSSW.Distill
