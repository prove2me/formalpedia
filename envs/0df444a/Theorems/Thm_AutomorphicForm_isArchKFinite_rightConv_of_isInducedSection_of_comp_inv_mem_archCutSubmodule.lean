-- Prove2me | Theorems.Thm_AutomorphicForm_isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
-- name    : AutomorphicForm.isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/391ce8b1-dd39-5860-8aa7-55c8f8561976
-- title:
--   Right convolution with an archimedean-type test function is K-finite
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}_F$ for its adele ring and $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, and let $\chi_1,\chi_2 \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be group homomorphisms. Let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and satisfy `IsInducedSection`, i.e. $\varphi(bg) = \chi_1(b_{00})\,\chi_2(b_{11})\,\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (the matrices in $\mathrm{GL}_2(\mathbb{A}_F)$ with vanishing $(1,0)$ entry), where $b_{00}, b_{11}$ are the diagonal entries of $b$ viewed as units via `borelDiagFst`, `borelDiagSnd`. Let $f \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous with compact support, and let `tys` be an `ArchTypeFamily F`: for each infinite place $w$ of $F$ a natural number $\mathrm{card}(w)$ together with $\mathrm{card}(w)$ objects `ArchRepAt F w`, each consisting of an $n \in \mathbb{N}$ and a complex representation $\rho$ of `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$. Assume that $x \mapsto f(x^{-1})$ lies in `archCutSubmodule F tys`, the intersection over all infinite places $w$ of the supremum over $i$ of the submodules `typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w i).ρ`. The conclusion is `IsArchKFinite F (rightConv F φ f)`: for every infinite place $w$ the function $g \mapsto \int \varphi(gx) f(x)\,dx$, the integral taken against the adelic Haar measure `AdelicHaar.adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_F)$ with its Borel structure, satisfies the finiteness condition `RightTranslatesSpanFinite` for the subgroup `archRowIsometrySubgroup F w`.
--
--   This is the statement that right convolution of a section of an induced space against a compactly supported test function of prescribed archimedean types produces a $K_\infty$-finite function, the finiteness being asserted for the full archimedean row-isometry groups `archRowIsometrySubgroup F w` while the type condition on the test function is phrased in terms of the subgroups `rowIsometrySubgroup₀`. It feeds the constructions of convolution operators and pseudo-Eisenstein series, in particular the expansion of a right convolution along an orthonormal family and the Paley–Wiener style compatibility statement for convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open AutomorphicForm

theorem AutomorphicForm.isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F]
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (_hφc : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (tys : ArchTypeFamily F) (_hfty : (fun x => f x⁻¹) ∈ archCutSubmodule F tys) :
    IsArchKFinite F (rightConv F φ f) := by sorry
