-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/074d0e05-ea14-519c-9c11-409bb67217ae
-- title:
--   Existence of slab fundamental domains for GL₂
-- statement:
--   Let $F$ be a number field (a field with a `NumberField` instance, so of characteristic zero and finite over $\mathbb{Q}$), and let $\mathrm{GL}_2(\mathbb{A}_F)$ denote `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over the adele ring of $F$, measurable via its Borel structure. The assertion is that there exist real numbers $\alpha,\beta$ and a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfying the four conditions packaged in `IsSlabFundamentalDomain F α β Φ₀`: first $0 < \alpha$; second $\alpha < \beta$; third $\Phi_0$ is contained in the determinant slab `detNormSlab F α β`, the set of $g$ whose idele norm $\lVert \det g\rVert_{\mathbb{A}}$ (given by [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) lies in the closed interval $[\alpha,\beta]$; and fourth $\Phi_0$ is a fundamental domain, in Mathlib's measure-theoretic sense, for the action of the range of `globalPoints (𝓞 F) F`, that is of the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2(\mathbb{A}_F)$ under the map induced by $F \to \mathbb{A}_F$, on $\mathrm{GL}_2(\mathbb{A}_F)$ equipped with the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` restricted to that slab. No explicit values of $\alpha$ and $\beta$ are asserted beyond $0 < \alpha < \beta$.
--
--   This is the existence of an exact fundamental domain for $\mathrm{GL}_2(F)$ acting on a region of $\mathrm{GL}_2(\mathbb{A}_F)$ with adelic determinant norm confined to a compact interval of positive reals, a reduction-theory statement in the style of the classical theory of fundamental domains for arithmetic groups. It provides the carrier on which the $L^2$-theory of the cuspidal spectrum is set up, and is invoked by the statements about cuspidal constituents and isotypic cusp submodules that extract eigenvectors of right convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain
    (F : Type) [Field F] [NumberField F] :
    ∃ (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)), IsSlabFundamentalDomain F α β Φ₀ := by sorry
