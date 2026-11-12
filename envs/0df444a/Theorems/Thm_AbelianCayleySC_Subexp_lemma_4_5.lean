-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_lemma_4_5
-- name    : AbelianCayleySC.Subexp.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:16.199174+00:00
-- url     : https://prove2.me/theorems/bdd76457-ce65-46ec-8058-40d1841b5f47
-- title:
--   Lemma 4.5 — one step of the geometric descent $\beta(\chi)\le\frac b4\lambda(\chi)+\beta(b\chi)/b$
-- statement:
--   Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph and $b\ge2$ an integer. For every character $\chi$ (the trivial one included),
--
--   $$\beta(\chi)\le\frac b4\,\lambda(\chi)+\frac{\beta(b\chi)}b,$$
--
--   where $b\chi$ is the $b$-th power of $\chi$.
--
--   It is the $T=0$ case of Proposition 4.3 and the induction step of its proof.
--
--   Differences from the source:
--   - encoding: dual group written additively: χ+γ, kχ, −χ, trivial character 0 → Mathlib AddChar Γ ℂ under pointwise multiplication: χ * γ, χ ^ k, χ⁻¹, 1; reason: the same group of characters in Mathlib's notation
--   - encoding: λ(χ) = 1 − α(χ), a complex expression that is real because S = −S → λ(χ) stored as the real number 1 − Re α(χ); reason: α(χ) is real for symmetric S, so 1 − α(χ) = 1 − Re α(χ) on every instance
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.11, Lemma 4.5

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Lemma 4.5** (p.11). For an integer `b ≥ 2` and every character `χ`,
`β(χ) ≤ (b/4) λ(χ) + β(bχ)/b`; the paper's `bχ` is `χ ^ b`. -/
theorem lemma_4_5 {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Finset Γ) (hS : IsSymmetricSet S) (b : ℕ) (hb : 2 ≤ b) (χ : AddChar Γ ℂ) :
    charBeta S χ ≤ (b : ℝ) / 4 * charLam S χ + charBeta S (χ ^ b) / (b : ℝ) := by sorry

end AbelianCayleySC.Subexp
