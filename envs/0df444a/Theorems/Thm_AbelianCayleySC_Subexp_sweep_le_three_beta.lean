-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_sweep_le_three_beta
-- name    : AbelianCayleySC.Subexp.sweep_le_three_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:36.146463+00:00
-- url     : https://prove2.me/theorems/8ed8c526-6fac-4055-9400-be89e1a8228e
-- title:
--   §4.2 display (p.10) — $\phi(\mathrm{Sweep}(\chi))\le3\beta(\chi)$
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph and $\chi$ a non-trivial character of order $m$. With $\beta(\chi)=\mathbb E_{s\sim S}[|\eta_\chi(s)|_m]/m$,
--
--   $$\phi\big(\mathrm{Sweep}(\chi)\big)\le3\,\beta(\chi).$$
--
--   It lets the analysis work with $\beta$, which behaves well under passing from $\chi$ to its multiples, instead of the conductance itself.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - encoding: χ of order m, with Sweep(χ) = η_χ^{-1}({0,…,⌊m/2⌋−1}) and φ(Q) defined for non-empty Q only → hypothesis χ ≠ 1 (equivalently m ≥ 2); reason: for χ = 1 Sweep(χ) = ∅ and φ(∅) and 1/⌊m/2⌋ are undefined; the hypothesis excludes only that undefined case
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.10, §4.2, unnumbered display after the definition of β

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **§4.2, display on p.10.** For a non-trivial character `χ`, `φ(Sweep(χ)) ≤ 3β(χ)` in
`Cay(Γ, S)`. -/
theorem sweep_le_three_beta {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (χ : AddChar Γ ℂ) (hχ : χ ≠ 1) :
    conductanceSet (cayAdj S) S.card (sweep χ) ≤ 3 * charBeta S χ := by sorry

end AbelianCayleySC.Subexp
