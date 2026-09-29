-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat
-- name    : AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/65801fb5-1300-5496-a939-038fed11c99b
-- title:
--   Flat involution preserves factorizable test functions on GL₂(A_F)
-- statement:
--   Let $F$ be a number field, let $\sigma$ be a real number, and let $f$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$ (that is, on `AdelicGL2 (𝓞 F) F`, the general linear group of degree $2$ over `AdeleRing (𝓞 F) F`). Assume $f$ is a factorizable test function in the sense of `IsFactorizableTestFn`: there are functions $f_\infty$ on $\mathrm{GL}_2$ of the infinite adele ring and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adele ring such that $f_\infty$ is of the form $\Phi \circ \mathrm{archEntries}$ for some $C^\infty$ function $\Phi$ on matrices over the mixed space of $F$ and has compact support, $f_{\mathrm{fin}}$ is locally constant with compact support, and $f(g) = f_\infty(\mathrm{glArch}\, g)\, f_{\mathrm{fin}}(\mathrm{glFin}\, g)$ for all $g$, where $\mathrm{glArch}$ and $\mathrm{glFin}$ are the group homomorphisms induced on $\mathrm{GL}_2$ by the projections of the adeles to the infinite and to the finite adeles. The conclusion is that the function $\mathrm{flat}\,F\,\sigma\,f$, namely $y \mapsto \overline{f(y^{-1})}\cdot \|\det y\|^{-\sigma}$, where $\|\cdot\|$ denotes [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the real number given by the distributive Haar character of the idele acting on the adele ring, is again a factorizable test function in the same sense.
--
--   The function $f^{\flat}$ is the kernel of the adjoint of convolution by $f$ with respect to the $\sigma$-weighted pairing used in the cuspidal spectral theory of $\mathrm{GL}_2$ over a number field; this lemma says that the class of factorizable (pure tensor) test functions is stable under that operation. It is used in the construction of the orthogonal complement of the closed cuspidal subrepresentation and in the further stability statements for conjugate-inverse test functions and for level-spherical functions of a given character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat.lean

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

theorem AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (flat F σ f) := by sorry
