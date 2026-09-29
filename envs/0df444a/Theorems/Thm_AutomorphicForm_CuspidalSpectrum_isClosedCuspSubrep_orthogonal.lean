-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal
-- name    : AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ca4a704f-e123-59b1-9f8d-0d3a670d8ee0
-- title:
--   Orthogonal complement of a closed cuspidal subrepresentation
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_F)$ satisfy `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, every $g\in\Phi_0$ has idèle norm of $\det g$ in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2(\mathbb{A}_F)$ on the adelic Haar measure restricted to that determinant slab. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{\sigma}$ for all $z$. Inside the Hilbert space $L^2$ of the weighted measure attached to $\Phi_0$ and $\sigma$, let $\mathcal{H}^{\mathrm{cusp}}$ be `cuspSubcarrier`, the topological closure of the image of the continuous smooth cuspidal automorphic members of character $\xi$. Let $M$ be a $\mathbb{C}$-submodule of $\mathcal{H}^{\mathrm{cusp}}$ which is a closed cusp subrepresentation: $M$ is closed, and every continuous linear endomorphism $S$ of $\mathcal{H}^{\mathrm{cusp}}$ that is a cusp lift of right translation by a finite adelic element, of right translation by an archimedean row-isometry element at an infinite place, or of right convolution by a factorizable, archimedean-bi-finite test function, satisfies $S(M)\subseteq M$. The conclusion is that the orthogonal complement $M^{\perp}$ of $M$ in $\mathcal{H}^{\mathrm{cusp}}$ is again a closed cusp subrepresentation for the same data.
--
--   This is the standard fact that the orthogonal complement of an invariant closed subspace of a unitary-type representation is again invariant, here in the form needed for the cuspidal $L^2$-spectrum of $\mathrm{GL}_2$ over a number field: the relevant adjoints of the lifted translation and convolution operators are again, up to a positive scalar, lifts of operations of the same three kinds. It feeds the decomposition of the cuspidal sub-carrier into irreducible pieces and the isotypic recognition statements built on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ Mᗮ := by sorry
