-- Prove2me | Theorems.Thm_DenseSL2_exists_elliptic_infinite_order_of_dense
-- name    : DenseSL2.exists_elliptic_infinite_order_of_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:56:59.111858+00:00
-- url     : https://prove2.me/theorems/fc771d50-9a93-48ac-bdf9-dfe79fbacde1
-- title:
--   A dense subgroup of SL₂(ℝ) contains an elliptic element of infinite order
-- statement:
--   Let $\Gamma$ be a dense subgroup of $\mathrm{SL}_2(\mathbb R)$. Then $\Gamma$ contains an element $a$ with $|\operatorname{tr} a| < 2$ such that $a^n \ne 1$ and $a^n \ne -1$ for every integer $n \ge 1$: an elliptic element whose image in $\mathrm{PSL}_2(\mathbb R)$ has infinite order. (The second condition already follows from the first, since $a^n = -1$ gives $a^{2n} = 1$; both are stated.)
--
--   $\mathrm{SL}_2(\mathbb R)$ is `Matrix.SpecialLinearGroup (Fin 2) ℝ` with its topology as a subspace of the $2 \times 2$ real matrices; $\Gamma$ need not be countable.
--
--   *Context.* This is the step of the Carrière–Ghys theorem (`CarriereGhys.not_isAmenableRel_orbit_of_dense`) that produces a conservative element. The proof chooses $A, B \in \Gamma$ by density and iterates $B_{n+1} = B_n A B_n^{-1}$ as in the proof of Jørgensen's inequality (Jørgensen 1976), which gives nontrivial elements of a finitely generated subgroup of $\Gamma$ converging to $1$. If every elliptic element of that subgroup had finite order, its traces would be numbers $z + z^{-1}$ with $z$ a root of unity lying in a finitely generated subring of $\mathbb R$, a finite set (`CyclotomicTrace.finite_add_inv_rootOfUnity`); pairing traces against four linearly independent elliptic elements then forces the converging elements to equal $1$.
-- source:
--   Standalone lemma, a step of the proof of CarriereGhys.not_isAmenableRel_orbit_of_dense (the Carrière–Ghys theorem as stated in Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, Theorem 2.2); the proof uses Jørgensen's iteration from Jørgensen, T., On discrete groups of Möbius transformations, Amer. J. Math. 98 (1976) 739–749, https://doi.org/10.2307/2373814

import Mathlib

namespace DenseSL2

theorem exists_elliptic_infinite_order_of_dense (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hΓ : Dense (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))) :
    ∃ a ∈ Γ, |Matrix.trace (a : Matrix (Fin 2) (Fin 2) ℝ)| < 2 ∧
      ∀ n : ℕ, 0 < n → a ^ n ≠ 1 ∧ a ^ n ≠ -1 := by
  sorry

end DenseSL2
