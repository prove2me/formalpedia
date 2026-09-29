-- Prove2me | Theorems.Thm_BrinSquier_no_free_subgroup_of_rank_two
-- name    : BrinSquier.no_free_subgroup_of_rank_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:20:23.867502+00:00
-- url     : https://prove2.me/theorems/51a364aa-e4df-491c-8c74-e4c5fbd19853
-- title:
--   No two piecewise-linear homeomorphisms with finitely many breakpoints form a free basis (Theorem 3.1: PLF(ℝ) has no free subgroup of rank greater than one)
-- statement:
--   For any two piecewise-linear homeomorphisms $f,g$ of $\mathbb{R}$ with finitely many breakpoints, the homomorphism from the free group of rank two sending its generators to $f$ and $g$ is **never injective**.
--
--   $$F_2 \longrightarrow \mathrm{PLF}(\mathbb{R}), \qquad a \mapsto f, \quad b \mapsto g\qquad\text{is never injective.}$$
--    Equivalently — and this is how Brin and Squier open their Section 3 — **any two elements of $\mathrm{PLF}(\mathbb{R})$ satisfy a nontrivial relation**: some nonempty reduced word in $f$, $g$ and their inverses is the identity.
--
--   Since a free group of rank greater than one contains one of rank two, and since $\mathrm{PLF}(\mathbb{R})$ is closed under products and inverses, this is exactly their Theorem (3.1): $\mathrm{PLF}(\mathbb{R})$ contains no free subgroup of rank greater than $1$.
--
--   **Why it matters.** Thompson's group $F$ sits inside $\mathrm{PLF}(\mathbb{R})$, so $F$ too has no non-abelian free subgroup. Brin and Squier set out to decide whether $F$ is a finitely presented counterexample to von Neumann's conjecture, and called this result half a success: it settles that $F$ cannot be shown non-amenable by exhibiting a free subgroup. Whether $F$ is amenable remains open.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, Theorem (3.1).

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem no_free_subgroup_of_rank_two (f g : ℝ ≃o ℝ) (hf : IsPLF f) (hg : IsPLF g) :
    ¬ Function.Injective (FreeGroup.lift ![f, g]) := by
  sorry

end BrinSquier
