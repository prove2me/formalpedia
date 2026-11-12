-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_fact_3_3
-- name    : AbelianCayleySC.Subexp.fact_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:00.172006+00:00
-- url     : https://prove2.me/theorems/4f0cc770-8137-40c2-b59a-4d5a43a97cf3
-- title:
--   Fact 3.3 — characters are a common orthogonal eigenbasis of every abelian Cayley graph
-- statement:
--   Let $\Gamma$ be a finite abelian group and $S=-S\subseteq\Gamma$, and let $G=\mathrm{Cay}(\Gamma,S)$ with normalized adjacency matrix $A(G)$ and normalized Laplacian $L(G)=I-A(G)$, acting on functions $\Gamma\to\mathbb C$. Then:
--
--   1. distinct characters are orthogonal: $\sum_{x\in\Gamma}\chi(x)\overline{\gamma(x)}=0$ for $\chi\ne\gamma$;
--   2. the characters are linearly independent and span $\mathbb C^\Gamma$, so they form a basis;
--   3. for every character $\chi$,
--   $$A(G)\,\chi=\alpha(\chi)\,\chi,\qquad L(G)\,\chi=\lambda(\chi)\,\chi,\qquad \alpha(\chi)=\frac1{|S|}\sum_{s\in S}\chi(s),\ \lambda(\chi)=1-\alpha(\chi).$$
--
--   This is the spectral dictionary of the paper: it identifies the Laplacian spectrum of an abelian Cayley graph with the values $\lambda(\chi)$, and so links the eigenvalue count $\mathrm{mul}_\tau(G)$ of Theorem 2.1 with the character count $\mathrm{mul}_\tau$ of Theorems 4.1 and 4.6.
--
--   **Formalization Note** The real matrices act on complex vectors after casting their entries to $\mathbb C$.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - encoding: "a basis of orthogonal eigenvectors" → pairwise orthogonality for the counting inner product, linear independence, and span = ⊤, as three separate clauses; reason: the same content stated clause by clause
--   - encoding: λ(χ) = 1 − α(χ), a complex expression that is real because S = −S → λ(χ) stored as the real number 1 − Re α(χ); reason: α(χ) is real for symmetric S, so 1 − α(χ) = 1 − Re α(χ) on every instance
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.7, Fact 3.3

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Fact 3.3** (p.7). For a finite abelian group `Γ` and a symmetric `S ⊆ Γ`, the characters
of `Γ` are pairwise orthogonal, form a basis of `Γ → ℂ`, and each character `χ` is an
eigenvector of the normalized adjacency matrix `A(G)` of `G = Cay(Γ, S)` with eigenvalue
`α(χ) = (1/|S|) ∑_{s∈S} χ(s)` and of the normalized Laplacian `L(G)` with eigenvalue
`λ(χ) = 1 − α(χ)`. The real matrices act on complex vectors through `ℝ → ℂ`. -/
theorem fact_3_3 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) :
    (∀ χ γ : AddChar Γ ℂ, χ ≠ γ → ∑ x : Γ, χ x * (starRingEnd ℂ) (γ x) = 0) ∧
    LinearIndependent ℂ (fun χ : AddChar Γ ℂ => (χ : Γ → ℂ)) ∧
    Submodule.span ℂ (Set.range (fun χ : AddChar Γ ℂ => (χ : Γ → ℂ))) = ⊤ ∧
    ∀ χ : AddChar Γ ℂ,
      ((normAdj (cayAdj S) S.card).map (fun r : ℝ => (r : ℂ))).mulVec (χ : Γ → ℂ) =
          charAlpha S χ • (χ : Γ → ℂ) ∧
      ((normLap (cayAdj S) S.card).map (fun r : ℝ => (r : ℂ))).mulVec (χ : Γ → ℂ) =
          ((charLam S χ : ℝ) : ℂ) • (χ : Γ → ℂ) := by sorry

end AbelianCayleySC.Subexp
