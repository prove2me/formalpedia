-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isArchBiFinite
-- name    : AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ffbd9795-2023-5b50-9fbd-b85c84a73061
-- title:
--   Right convolution preserves principal level and archimedean cut
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, $N$ an ideal of $\mathcal{O}_F$ and $tys$ an archimedean type family for $F$, i.e. a cardinality $tys.\mathrm{card}(w)$ together with representations $tys.\mathrm{rep}(w,i)$ at each infinite place $w$. Throughout, the pins are `productionPinsOf` for $D$, with level groups $U(N) =$ `principalLevel` $(N) \sqcap$ `finiteAdelicGL2Subgroup`, that is the intersection of $\mathrm{levelOne}(N)$ with its conjugate by the Weyl element, intersected with the kernel of the map to the archimedean component, with Hecke generators $\mathrm{heckeGen}_v$ and window `adelicBox`; the measurable structure is the Borel structure and the measure the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$. Let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy: $f$ is a factorizable test function (a product of a smooth compactly supported archimedean factor and a finite test factor), $f$ is arch bi-finite for $tys$ (i.e. $x \mapsto f(x^{-1})$ lies in the archimedean cut submodule $\bigsqcap_w \bigsqcup_i \mathrm{archTypeSubmoduleAt}(w, tys.\mathrm{rep}(w,i))$ and $f$ lies in the dual cut submodule), and every $x$ with $f(x) \neq 0$ factors as $x = a k$ with $\mathrm{glFin}(a) = 1$ and $k \in U(N)$. Let $\varphi$ be continuous and right $U(N)$-invariant, $\varphi(g u) = \varphi(g)$ for all $g$ and all $u \in U(N)$. Then the right convolution $g \mapsto \int \varphi(g x) f(x)\,d\mu(x)$ is again right $U(N)$-invariant and lies in the archimedean cut submodule of $tys$.
--
--   This is the level-and-type preservation step for smoothing automorphic functions by a test function, in the variant where the level structure is given by the full principal congruence subgroups $K(N)$ cut down to the finite part. It is used in the analysis of principal-level isotypic cusp spaces, being cited by the results producing vectors as right convolutions and by the non-vanishing statement for the cuspidal spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isArchBiFinite.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    rightConv F φ f ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys := by sorry
