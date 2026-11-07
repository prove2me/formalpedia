-- Prove2me | Theorems.Thm_DynStrings_corollary_5_5_exclusive_symbols
-- name    : DynStrings.corollary_5_5_exclusive_symbols
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:28.705914+00:00
-- url     : https://prove2.me/theorems/a4a5d5ce-d8a7-4d93-bb6f-13ec8cda3bd7
-- title:
--   Corollary 5.5 — the number of exclusive symbols is $O(\Lambda(X\mid\mathcal C))$
-- statement:
--   There is an absolute constant $C_0$ such that for every string $X$, every finite collection $\mathcal C$ and every choice of the orders, the number of structural symbols exclusive to $X$ relative to $\mathcal C$ (labelling a node of $T(X)$ but of no $T(Y)$, $Y\in\mathcal C$) is at most
--
--   $$C_0\,\Lambda(X\mid\mathcal C).$$
--
--   This bounds the symbol count of $G(X\mid\mathcal C)$ deterministically; only the total arity of the exclusive tuples is left to the probabilistic analysis.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - encoding: the grammar: symbols labelling the nodes of T(S), the unfolding of the root → the unfolding of the symbols of the level word S_{κ(|S|)}; reason: by Fact 4.4 this level word is the single root for non-empty S, and it is empty for the empty string
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Corollary 5.5, p.22

import Mathlib
import Definitions.Def_DynStrings_Novelty

namespace DynStrings

/-- **Corollary 5.5**, p.22.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

For every string `X`, finite collection `𝒞`, and every choice of the orders, the number
of symbols exclusive to `X` relative to `𝒞` is `O(Λ(X | 𝒞))`. -/
theorem corollary_5_5_exclusive_symbols :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α : Type) [DecidableEq α] (X : List α) (𝒞 : Multiset (List α))
      (lt : ℕ → StrSym α → StrSym α → Prop), IsOrderFamily lt →
      ((excl lt X 𝒞).card : ℝ) ≤ C₀ * Lam X 𝒞 := by sorry

end DynStrings
