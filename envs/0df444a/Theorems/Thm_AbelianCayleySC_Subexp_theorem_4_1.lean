-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_theorem_4_1
-- name    : AbelianCayleySC.Subexp.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:11.006295+00:00
-- url     : https://prove2.me/theorems/504e2866-e16a-49be-818b-da67943ccb21
-- title:
--   Theorem 4.1 (= Theorem 2.2) — structured sparse cut $\mathrm{Sweep}(\chi)$ in high threshold rank
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph, $\tau>0$, and $\mathrm{mul}_\tau=|\{\chi\in\widehat\Gamma:\lambda(\chi)\le\tau\}|$. If $\mathrm{mul}_\tau>|\Gamma|^{2/3}$, then there is a non-trivial character $\chi\in\widehat\Gamma$ whose threshold rounding has conductance
--
--   $$\phi\big(\mathrm{Sweep}(\chi)\big)\le\frac{435}{2}\,\tau$$
--
--   in $G$.
--
--   This is the paper's main structural contribution: in the high-threshold-rank regime, an algebraically structured cut is already a constant-factor approximation, which handles the case that eigenspace enumeration cannot afford.
--
--   **Formalization Note** The paper writes $O(\tau)$; its proof (Theorem 4.6 with the display $\phi(\mathrm{Sweep}(\chi))\le3\beta(\chi)$) yields the constant $3\cdot145/2=435/2$.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - reading: φ(Sweep(χ)) ⩽ O(τ) → φ(Sweep(χ)) ≤ (435/2)·τ for every τ > 0; reason: the explicit constant of the paper's own proof: (145/2)τ from Theorem 4.6 times 3 from the §4.2 display
--   - encoding: λ(χ) = 1 − α(χ), a complex expression that is real because S = −S → λ(χ) stored as the real number 1 − Re α(χ); reason: α(χ) is real for symmetric S, so 1 − α(χ) = 1 − Re α(χ) on every instance
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.8, Theorem 4.1 (identical to Theorem 2.2, p.3)

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Theorem 4.1** (p.8; = Theorem 2.2, p.3), with the constant of its proof. For `τ > 0`, if
more than `|Γ|^{2/3}` characters satisfy `λ(χ) ≤ τ`, then some non-trivial character `χ` has
`φ(Sweep(χ)) ≤ (435/2)·τ` in `Cay(Γ, S)`. -/
theorem theorem_4_1 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (τ : ℝ) (hτ : 0 < τ)
    (hmul : (Fintype.card Γ : ℝ) ^ ((2 : ℝ) / 3) < (mulChar S τ : ℝ)) :
    ∃ χ : AddChar Γ ℂ, χ ≠ 1 ∧ conductanceSet (cayAdj S) S.card (sweep χ) ≤ 435 / 2 * τ := by sorry

end AbelianCayleySC.Subexp
