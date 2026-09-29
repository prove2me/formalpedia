-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
-- name    : AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/be7e34ec-b200-5aff-8986-13e6e778d20b
-- title:
--   Continuous cusp realisations admit no Hecke-generator translation eigenvalue
-- statement:
--   Let $F$ be a number field, $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and $\Psi$ a complex Hecke eigensystem for $F$, that is, a nonzero ideal $\mathfrak{n} = \Psi.\mathrm{level}$ of $\mathcal{O}_F$ together with families $a, b$ of complex numbers indexed by the finite places. Work at the pins `productionPinsOf` assembled from: the Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the window $D$, central subgroup $\top$ (all of $\mathbb{A}_F^\times$), level groups $N \mapsto \mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$, Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and the additive Haar measure conditioned on the adelic box. Let $R$ be a smooth cusp realisation of $\Psi$ at these pins: a function $\varphi = R.\mathrm{toFun} : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, nonzero at some point, with a central character on $\mathbb{A}_F^\times$, which is cuspidal automorphic and smooth for the finite part, is right invariant under $\mathrm{levelOne}(\mathfrak{n}) \cap \ker(\mathrm{glArch})$, and which, outside a finite exceptional set of places, satisfies the Hecke coset eigenvalue relation with eigenvalue $a(v)$ for a system of $|\mathcal{O}_F/v|+1$ coset representatives of that level group determined by $\mathrm{heckeGen}(v)$, and transforms by $b(v)$ under left translation by the central scalar $\det \mathrm{heckeGen}(v)$. Assume $\varphi$ is continuous, and let $v$ be a finite place with $v \nmid \mathfrak{n}$. Then there is no $c \in \mathbb{C}$ with $\varphi(g\,\mathrm{heckeGen}(v)) = c\,\varphi(g)$ for all $g \in \mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the form, for number fields, of the classical statement that a cuspidal automorphic form on $\mathrm{GL}_2$ cannot be an eigenvector for right translation by the Hecke generator at a place prime to the level, equivalently that cuspidal automorphic representations have no one-dimensional local components. It is used in the Langlands–Tunnell part of the development, where it feeds the bound on Satake parameters at places away from the level and the associated sum-of-squares estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

theorem AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Ψ)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Ψ R)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ Ψ.level) :
    ¬ ∃ c : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, R.toFun (g * heckeGen (𝓞 F) F v) = c * R.toFun g := by sorry
