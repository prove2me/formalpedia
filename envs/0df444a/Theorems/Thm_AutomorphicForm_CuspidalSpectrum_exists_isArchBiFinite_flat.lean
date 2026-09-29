-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a0594cb7-964a-508d-8d24-9093100f6591
-- title:
--   Archimedean bi-finiteness of the flat of a test function
-- statement:
--   Let $F$ be a number field, let $\sigma$ be a real number, let $\mathrm{tys}$ be an archimedean type family for $F$ (data consisting of a natural number $\mathrm{card}\,w$ for each infinite place $w$ of $F$ together with, for each $i < \mathrm{card}\,w$, an archimedean type at $w$, i.e. a dimension $n$ and a representation of `rowIsometrySubgroup₀` of the completion of $F$ at $w$ on $\mathbb{C}^{n}$), and let $f$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$. Assume $f$ is a factorizable test function: there are functions $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles such that $f_\infty$ is of the form $g \mapsto \Phi(\mathrm{archEntries}\,g)$ for some $\Phi$ of class $C^{\infty}$ on $2\times 2$ matrices over the mixed space of $F$ and has compact support, $f_{\mathrm{fin}}$ is locally constant with compact support, and $f(g) = f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for all $g$. Assume further that $f$ is archimedean-bi-finite of type $\mathrm{tys}$, meaning that $x \mapsto f(x^{-1})$ lies in the submodule $\bigsqcap_{w}\bigvee_{i}$ `archTypeSubmoduleAt` $(w,\mathrm{tys}.\mathrm{rep}\,w\,i)$ and $f$ itself lies in the corresponding submodule built from `archDualTypeSubmoduleAt`. The conclusion is that there exists an archimedean type family $\mathrm{tys}'$ for which the function $\mathrm{flat}\,\sigma\,f$, given by $y \mapsto \overline{f(y^{-1})}\cdot \|\det y\|^{-\sigma}$ with $\|\cdot\|$ the idele norm (the module of the distinguished Haar character of the adele ring), is archimedean-bi-finite of type $\mathrm{tys}'$.
--
--   The function $\mathrm{flat}\,\sigma\,f$ is the kernel adjoint to $f$ for the pairing twisted by $\|\det\|^{-\sigma}$; the statement records that passing to this adjoint preserves archimedean bi-finiteness, at the cost of replacing the given type family by another one (inversion interchanges the two finiteness clauses, and conjugation replaces the listed representations by their conjugates). It is used in the analysis of the orthogonal complement of the cuspidal subrepresentation, in [`AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal`](thm.html#AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ) (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F, IsArchBiFinite F tys' (flat F σ f) := by sorry
