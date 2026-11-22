-- Prove2me | Theorems.Thm_BellSampling_Learn_stabSet_subspace
-- name    : BellSampling.Learn.stabSet_subspace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:02.874985+00:00
-- url     : https://prove2.me/theorems/24eb3669-5030-45da-889a-bc71d905b129
-- title:
--   Learning stabilizer states, p. 2 — T is an n-dimensional linear subspace of F₂^{2n}
-- statement:
--   Let $\psi$ be an $n$-qubit stabilizer state and let $T=T(\psi)\subseteq\mathbb F_2^{2n}$ be the set of strings $t$ for which $\psi$ is an eigenvector of $\sigma_t$. Then $T$ is a linear subspace of $\mathbb F_2^{2n}$ and
--   $$\dim_{\mathbb F_2} T=n.$$
--
--   This is the linear-algebraic description of the stabilizer group: its $2^n$ elements, up to phases, are labelled by an $n$-dimensional subspace, and learning $\psi$ reduces to learning this subspace and a sign for each basis element.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Learning stabilizer states, "Let T denote the set of strings … Then T is an n-dimensional linear subspace of F₂^{2n}."

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem stabSet_subspace {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ W : Submodule (ZMod 2) (PStr n), (W : Set (PStr n)) = stabSet ψ ∧
      Module.finrank (ZMod 2) W = n := by sorry
end BellSampling.Learn
