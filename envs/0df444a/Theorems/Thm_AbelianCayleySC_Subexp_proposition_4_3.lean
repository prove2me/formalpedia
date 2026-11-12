-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_proposition_4_3
-- name    : AbelianCayleySC.Subexp.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:26.108254+00:00
-- url     : https://prove2.me/theorems/db205ec4-fcd9-4982-9a95-b12535cb2bc2
-- title:
--   Proposition 4.3 — eigenvalue bound for $\beta$ along a geometric progression
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph, and $b\ge2$, $T\ge0$ integers. For every character $\chi$,
--
--   $$\beta(\chi)\le\frac b4\sum_{j=0}^{T}b^{-j}\,\lambda\big(b^{j}\chi\big)+\frac{\beta\big(b^{T+1}\chi\big)}{b^{T+1}},$$
--
--   where $b^j\chi$ is the $b^j$-th power of $\chi$.
--
--   It bounds the rounding quantity $\beta(\chi)$ by Laplacian eigenvalues at the sparse set of multiples $b^j\chi$, which is what the additive-combinatorics argument of Theorem 4.6 can control.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - encoding: λ(χ) = 1 − α(χ), a complex expression that is real because S = −S → λ(χ) stored as the real number 1 − Re α(χ); reason: α(χ) is real for symmetric S, so 1 − α(χ) = 1 − Re α(χ) on every instance
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.10, Proposition 4.3 (proof printed as "Proof of Proposition 2.3", p.12)

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Proposition 4.3** (p.10). For integers `b ≥ 2`, `T ≥ 0` and every character `χ`,
`β(χ) ≤ (b/4) ∑_{j=0}^{T} b^{−j} λ(b^j χ) + β(b^{T+1} χ)/b^{T+1}`; `b^j χ` is `χ ^ (b ^ j)`. -/
theorem proposition_4_3 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (b T : ℕ) (hb : 2 ≤ b) (χ : AddChar Γ ℂ) :
    charBeta S χ ≤
      (b : ℝ) / 4 * ∑ j ∈ range (T + 1), ((b : ℝ) ^ j)⁻¹ * charLam S (χ ^ (b ^ j)) +
        charBeta S (χ ^ (b ^ (T + 1))) / (b : ℝ) ^ (T + 1) := by sorry

end AbelianCayleySC.Subexp
