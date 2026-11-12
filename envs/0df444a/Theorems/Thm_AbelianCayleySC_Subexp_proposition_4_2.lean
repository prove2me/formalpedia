-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_proposition_4_2
-- name    : AbelianCayleySC.Subexp.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:11.393469+00:00
-- url     : https://prove2.me/theorems/947283d5-8f14-4476-ba7e-014b81778b60
-- title:
--   Proposition 4.2 — exact conductance of the threshold rounding $\mathrm{Sweep}(\chi)$
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph and $\chi$ a non-trivial character of order $m\ge2$. With $\eta_\chi(s)\in\{0,\dots,m-1\}$ the exponent of $\chi(s)=e^{2\pi i\eta_\chi(s)/m}$ and $|\cdot|_m$ the modular distance, the conductance of $\mathrm{Sweep}(\chi)$ in $G$ is
--
--   $$\phi\big(\mathrm{Sweep}(\chi)\big)=\frac1{\lfloor m/2\rfloor}\,\mathbb E_{s\sim S}\big[|\eta_\chi(s)|_m\big].$$
--
--   It turns the conductance of a rounded character into an explicit average over the generators, the starting point of the eigenvalue bounds of §4.2.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - encoding: χ of order m, with Sweep(χ) = η_χ^{-1}({0,…,⌊m/2⌋−1}) and φ(Q) defined for non-empty Q only → hypothesis χ ≠ 1 (equivalently m ≥ 2); reason: for χ = 1 Sweep(χ) = ∅ and φ(∅) and 1/⌊m/2⌋ are undefined; the hypothesis excludes only that undefined case
--   - encoding: E_{s∼S}, the uniform average over S → (1/|S|)·∑_{s∈S}; reason: definition of the uniform average
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.10, Proposition 4.2

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Proposition 4.2** (p.10). For a non-trivial character `χ` of order `m`, the conductance of
`Sweep(χ)` in `Cay(Γ, S)` is `(1/⌊m/2⌋) · E_{s∼S}[|η_χ(s)|_m]`. -/
theorem proposition_4_2 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (χ : AddChar Γ ℂ) (hχ : χ ≠ 1) :
    conductanceSet (cayAdj S) S.card (sweep χ) =
      (1 / ((orderOf χ / 2 : ℕ) : ℝ)) *
        ((1 / (S.card : ℝ)) * ∑ s ∈ S, modDist (orderOf χ : ℝ) (charEta χ s : ℝ)) := by sorry

end AbelianCayleySC.Subexp
