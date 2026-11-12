-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_theorem_4_6
-- name    : AbelianCayleySC.Subexp.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:18.196262+00:00
-- url     : https://prove2.me/theorems/06f758f0-b72a-4d87-bcdf-23cdedc903ea
-- title:
--   Theorem 4.6 — a non-trivial character with $\beta=O(\tau)$ in high threshold rank
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph, $\tau>0$, and $\mathrm{mul}_\tau=|\{\chi\in\widehat\Gamma:\lambda(\chi)\le\tau\}|$. If $\mathrm{mul}_\tau>|\Gamma|^{2/3}$, then there is a non-trivial character $r\in\widehat\Gamma$ with
--
--   $$\beta(r)\le\frac{145}{2}\,\tau .$$
--
--   Combined with $\phi(\mathrm{Sweep}(\chi))\le3\beta(\chi)$ it gives Theorem 4.1.
--
--   **Formalization Note** The paper writes $O(\tau)$; its proof yields the constant $145/2$.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - reading: "there exists an r ∈ Γ" → there exists a character r ∈ Γ̂ with r ≠ 1; reason: β is defined on characters; as printed the statement is trivial at r = 0 (β(0) = 0), while the proof constructs r = a₀ − b₀ ≠ 0 (p.13) and Theorem 4.1 needs a non-trivial r; this reading is the stronger one
--   - reading: β(r) = O(τ) → β(r) ≤ (145/2)·τ for every τ > 0; reason: the explicit constant of the paper's own proof (p.13): λ(6^t r) ≤ 4^{t+2}τ and Proposition 4.3 with b = 6 give β(r) ≤ 72τ + 1/(2·6^{T+1}), and T ≥ 2 with 6^{T+1} ≥ 1/τ gives ≤ (145/2)τ
--   - encoding: λ(χ) = 1 − α(χ), a complex expression that is real because S = −S → λ(χ) stored as the real number 1 − Re α(χ); reason: α(χ) is real for symmetric S, so 1 − α(χ) = 1 − Re α(χ) on every instance
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.12, Theorem 4.6 (proof pp.12–13)

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Theorem 4.6** (p.12), with the constant of its proof. For `τ > 0`, if more than
`|Γ|^{2/3}` characters satisfy `λ(χ) ≤ τ`, then some non-trivial character `r` has
`β(r) ≤ (145/2)·τ`. -/
theorem theorem_4_6 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (τ : ℝ) (hτ : 0 < τ)
    (hmul : (Fintype.card Γ : ℝ) ^ ((2 : ℝ) / 3) < (mulChar S τ : ℝ)) :
    ∃ r : AddChar Γ ℂ, r ≠ 1 ∧ charBeta S r ≤ 145 / 2 * τ := by sorry

end AbelianCayleySC.Subexp
