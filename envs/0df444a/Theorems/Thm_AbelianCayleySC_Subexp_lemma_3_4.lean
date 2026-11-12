-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_lemma_3_4
-- name    : AbelianCayleySC.Subexp.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:05.630729+00:00
-- url     : https://prove2.me/theorems/8ad77459-0c55-414a-a09a-2dae3284db1d
-- title:
--   Lemma 3.4 — $\sqrt{\lambda}$ is subadditive on the dual group
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph ($\Gamma$ finite abelian, $S=-S$), and let $\lambda(\chi)=1-\frac1{|S|}\sum_{s\in S}\chi(s)$ be the Laplacian eigenvalue of the character $\chi$. For all characters $\chi,\gamma$,
--
--   $$\sqrt{\lambda(\chi+\gamma)}\le\sqrt{\lambda(\chi)}+\sqrt{\lambda(\gamma)},$$
--
--   where $\chi+\gamma$ is the pointwise product of the two characters.
--
--   It shows that the small Laplacian eigenvalues are additively structured ($\mathrm{low}_\tau+\mathrm{low}_\tau\subseteq\mathrm{low}_{4\tau}$), the key input to the pigeonhole argument of Theorem 4.6.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - encoding: λ(χ) = 1 − α(χ), a complex expression that is real because S = −S → λ(χ) stored as the real number 1 − Re α(χ); reason: α(χ) is real for symmetric S, so 1 − α(χ) = 1 − Re α(χ) on every instance
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.7, Lemma 3.4

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Lemma 3.4** (p.7). In `Cay(Γ, S)`, `√λ(χ + γ) ≤ √λ(χ) + √λ(γ)` for all characters
`χ, γ`; the paper's `χ + γ` is the pointwise product `χ * γ`. -/
theorem lemma_3_4 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (χ γ : AddChar Γ ℂ) :
    Real.sqrt (charLam S (χ * γ)) ≤ Real.sqrt (charLam S χ) + Real.sqrt (charLam S γ) := by sorry

end AbelianCayleySC.Subexp
