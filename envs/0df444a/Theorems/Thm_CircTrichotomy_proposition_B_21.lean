-- Prove2me | Theorems.Thm_CircTrichotomy_proposition_B_21
-- name    : CircTrichotomy.proposition_B_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:49.912201+00:00
-- url     : https://prove2.me/theorems/00d8dbc8-1d6e-497a-91d9-7b2300756bd7
-- title:
--   Proposition B.21 — modular disjoint monomials are $\mathcal L^1[\mathcal B_{[<,+\omega]}]$-definable
-- statement:
--   **Proposition B.21.** For every $k$-modular disjoint monomial $L$ over a finite non-empty alphabet $\Sigma$ there is a sentence $\varphi\in\mathcal L^1[\mathcal B_{[<,+\omega]},\Sigma,<,+\omega,\mathrm{mod},\min,\max]$ with
--   $$L(\varphi)=L\cap\Sigma^+.$$
--
--   It is a step of the direction (7) ⇒ (8) of Theorem 2.8.
--
--   Differences from the source:
--   - encoding: L¹ formulas with variables x₀, …, x_{k−1} in quantifier arguments → L1Form written in one variable x; reason: every subformula has at most one free variable; renaming bound variables changes no semantics
--   - encoding: a formula φ with L(φ) = L ∩ Σ⁺ → a sentence φ (IsSentence) with L1Lang φ = L ∩ Σ⁺; reason: L(φ) is defined for sentences (p.20)
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Proposition B.21, p.30

import Mathlib
import Definitions.Def_CircTrichotomy_IsModDisjointMonomial
import Definitions.Def_CircTrichotomy_L1Form
import Definitions.Def_CircTrichotomy_BoundedDefinable

set_option autoImplicit false

namespace CircTrichotomy

/-- **Proposition B.21** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Proposition B.21, p.30): "For every k-modular disjoint monomial L,
there exists a formula φ ∈ L¹[B_{[<,+ω]}, Σ, <, +ω, mod, min, max] such that L(φ) = L ∩ Σ⁺."

**Formalization Note** `φ` is a sentence (`L(φ)` is defined for sentences, p.20); the fragment is
`InFragment ordVocab (BoundedDefinable ordRels)` and `L(φ)` is `L1Lang φ`. -/
theorem proposition_B_21 {α : Type} [Fintype α] [Nonempty α] (K : Language α)
    (hK : IsModDisjointMonomial K) :
    ∃ φ : L1Form α, φ.IsSentence ∧ φ.InFragment ordVocab (BoundedDefinable ordRels) ∧
      L1Lang φ = {w | w ∈ K ∧ w ≠ []} := by sorry

end CircTrichotomy
