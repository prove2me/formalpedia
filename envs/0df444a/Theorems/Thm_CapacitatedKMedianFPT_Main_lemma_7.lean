-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_7
-- name    : CapacitatedKMedianFPT.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:09.665119+00:00
-- url     : https://prove2.me/theorems/6a53d85d-0217-41e4-b746-5fd0b083d9c7
-- title:
--   Lemma 7 — a transversal of the supports beats the expected value of independent random sets
-- statement:
--   Let $F=F_1\cup\dots\cup F_k$ with the $F_i$ mutually disjoint, and let $v:2^F\to\mathbb R$ be monotone and submodular. For each $i\in[k]$ let $D_i$ be a probability distribution over subsets of $F_i$, and let $X_1,\dots,X_k$ be sampled independently from $D_1,\dots,D_k$. If $0<\mathbb E[|X_i|]\le1$ for all $i$, then there is a set $\{x_1,\dots,x_k\}\subseteq F$ with
--
--   1. $\Pr[x_i\in X_i]>0$ (in particular $x_i\in F_i$) for all $i\in[k]$, and
--   2. $v(\{x_1,\dots,x_k\})\ge\mathbb E[v(X_1\cup\dots\cup X_k)]$.
--
--   No normalization or sign is assumed on $v$, and each $X_i$ may have arbitrary internal correlation. The lemma is the rounding step of the capacity-preserving maximization (Corollary 1).
--
--   **Formalization Note** The ground type is exactly $F$; distributions are real mass functions and the expectation is the finite sum over the product law.
--
--   Differences from the source:
--
--   - encoding: random subsets X_i ∼ D_i, independent → mass functions D_i on subsets with support in F_i; the expectation of v(∪X_i) as the sum over the product law; reason: the same distributions; all expectations are finite
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 16, Lemma 7 (the final bullet's closing parenthesis is missing in the PDF); proof p. 17

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_RandomSets
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Lemma 7** (p. 16). Let the ground set be the disjoint union `F_1 ∪ ⋯ ∪ F_k` and
`v : 2^F → ℝ` monotone submodular. Let `X_i ∼ D_i` be independent random subsets of `F_i` with
`0 < E|X_i| ≤ 1`. Then there are `x_1, …, x_k` with `Pr[x_i ∈ X_i] > 0` for all `i` and
`v({x_1, …, x_k}) ≥ E[v(X_1 ∪ ⋯ ∪ X_k)]`. -/
theorem lemma_7 {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (F : Fin k → Finset α)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j))) (hcover : ∀ x, ∃ i, x ∈ F i)
    (v : Finset α → ℝ) (hmono : SubsamplingSM.Offline.IsMonotoneSetFn v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (D : Fin k → Finset α → ℝ) (hD : ∀ i, IsSubsetLaw (D i) (F i))
    (hE : ∀ i, 0 < expectedCard (D i) ∧ expectedCard (D i) ≤ 1) :
    ∃ x : Fin k → α, (∀ i, 0 < inclusionProb (D i) (x i)) ∧
      expectedUnionValue D v ≤ v (Finset.univ.image x) := by sorry

end CapacitatedKMedianFPT.Main
