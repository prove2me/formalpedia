-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
-- name    : AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/58166320-c732-5955-8a2d-3f9c02c0e9c5
-- title:
--   Smoothing by a test function supported in the level group
-- statement:
--   Let $F$ be a number field and write $G = \mathrm{GL}_2(\mathbb{A}_F)$, realised as the general linear group of degree $2$ over the adele ring of $\mathcal{O}_F$. Fix a set $D \subseteq G$, an ideal $N$ of $\mathcal{O}_F$ and a family `tys` of archimedean types, i.e. for each infinite place $w$ of $F$ a natural number and that many representations of the local archimedean datum at $w$. The carrier data is `productionPinsOf` for $D$, the assignment $N \mapsto$ `levelOne` $(N) \sqcap$ `finiteAdelicGL2Subgroup` $F$, the Hecke generators `heckeGen` and the box `adelicBox` $F$; its level group at $N$ is $U = \{u \in G : u$ lies in the level-one subgroup attached to $N$ and has trivial archimedean component$\}$, i.e. the intersection of `levelOne` $(N)$ with the kernel of `glArch`. Let $f : G \to \mathbb{C}$ be a factorizable test function (a product of an archimedean factor that is smooth in the matrix entries and compactly supported with a finite factor satisfying `IsFinTestFactor`), assumed archimedean bi-finite of type `tys` (that is, $x \mapsto f(x^{-1})$ lies in the archimedean cut submodule $\bigsqcap_w \bigsqcup_i$ `archTypeSubmoduleAt` for `tys`, and $f$ lies in the dual cut submodule), and assume every point $x$ of the support of $f$ factors as $x = a k$ with `glFin` $(a) = 1$ and $k \in U$. Let $\varphi : G \to \mathbb{C}$ be continuous and right $U$-invariant, i.e. $\varphi(gu) = \varphi(g)$ for all $g \in G$, $u \in U$. Then the right convolution `rightConv` $F\,\varphi\,f$, given by $g \mapsto \int_G \varphi(gx) f(x)\,d\mu(x)$ for the adelic Haar measure on $G$, is again right $U$-invariant and lies in the archimedean cut submodule for `tys`.
--
--   This is the function-level statement that smoothing a continuous level-$N$-invariant function by an archimedean bi-finite test function supported in the level group preserves right invariance under the level group and forces the prescribed archimedean types, with no type hypothesis on $\varphi$ itself. It is used in the constituent-cut arguments for cuspidal automorphic forms on $\mathrm{GL}(2)$, notably in the statements producing a test function with `rightConv` equal to the given form and in the stability of the isotypic cuspidal submodule under smoothing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    rightConv F φ f ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys := by sorry
