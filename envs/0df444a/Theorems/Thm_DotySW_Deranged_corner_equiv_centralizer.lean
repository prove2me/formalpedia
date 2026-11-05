-- Prove2me | Theorems.Thm_DotySW_Deranged_corner_equiv_centralizer
-- name    : DotySW.Deranged.corner_equiv_centralizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:12.941777+00:00
-- url     : https://prove2.me/theorems/8a2b891c-770d-46f2-aa33-9b6699c37e5a
-- title:
--   Eq. (17) — $\mathcal C\simeq e\mathcal B^{(n)}_{r,r}e$ for $n\ge2r$
-- statement:
--   Let $n\ge 2r$ and $\mathcal C=\mathrm{End}_{\mathrm{GL}_n}(\mathfrak{sl}_n^{\otimes r})$. The set $e\mathcal B^{(n)}_{r,r}e$ is closed under the product and contains $e$, and restricting $\sigma$ to $\mathfrak{sl}_n^{\otimes r}$ gives a bijective linear map
--
--   $$
--   e\mathcal B^{(n)}_{r,r}e\xrightarrow{\ \sim\ }\mathcal C
--   $$
--
--   that is multiplicative and sends $e$ to the identity. Thus the centralizer of $\mathrm{GL}_n$ on the adjoint tensor power is the deranged algebra.
--
--   **Formalization Note** The deranged algebra is a subspace of the walled Brauer algebra, so the isomorphism of unital algebras is written as a linear equivalence with separate multiplicative and unital clauses.
--
--   Differences from the source:
--   - encoding: the algebra isomorphism $\mathcal C\simeq e\mathcal B^{(n)}_{r,r}e$ → a linear equivalence with multiplicativity and unitality stated as clauses; reason: `corner` is a subspace of the walled Brauer algebra with unit e, not a subalgebra with the unit of the ambient algebra
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, Eq. (17), p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_rhoSl
import Definitions.Def_DotySW_Deranged_corner
import Definitions.Def_DotySW_Deranged_ActsBy

namespace DotySW.Deranged

/-- **Eq. (17): `C ≃ e B^{(n)}_{r,r} e` for `n ≥ 2r`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, Eq. (17), p. 11.

The deranged algebra is closed under the product of `B^{(n)}_{r,r}` and has unit `e`, and restriction
of `σ` to `sl_n^{⊗r}` is an isomorphism of unital algebras from it onto
`C = End_{GL_n}(sl_n^{⊗r})`.

**Formalization Note** `corner` is a subspace, so the isomorphism is a linear equivalence that is
stated to be multiplicative and unital. `C` is the commutant of the operators `rhoSl n r g`. -/
theorem corner_equiv_centralizer (n r : ℕ) (h : 2 * r ≤ n) :
    ∃ (hmul : ∀ x y : corner n r, x.1 * y.1 ∈ corner n r) (he : eIdem n r ∈ corner n r)
      (φ : corner n r ≃ₗ[ℂ] Subalgebra.centralizer ℂ (Set.range (rhoSl n r))),
      (∀ x, ActsBy n r x.1 (φ x).1) ∧
      (∀ x y, φ ⟨x.1 * y.1, hmul x y⟩ = φ x * φ y) ∧
      φ ⟨eIdem n r, he⟩ = 1 := by sorry

end DotySW.Deranged
