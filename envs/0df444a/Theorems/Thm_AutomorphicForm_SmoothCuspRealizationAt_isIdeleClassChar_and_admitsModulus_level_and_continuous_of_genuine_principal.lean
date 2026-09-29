-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine_principal
-- name    : AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/0851faf7-bc3a-5f7b-aefd-0d07086b3e05
-- title:
--   Central character of a principal-level smooth cusp realization
-- statement:
--   Let $F$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, let $\mathrm{gen}$ assign to each finite place $v$ of $F$ an element of $\mathrm{GL}_2(\mathbb{A}_F)$, let $B$ be a subset of $\mathbb{A}_F$, and let $\Phi$ be a Hecke eigensystem over $\mathbb{C}$, i.e. a nonzero ideal $\Phi.\mathrm{level}\subseteq\mathcal{O}_F$ together with families of complex numbers $a_v$, $b_v$ indexed by the finite places. Form the carrier pins `productionPinsOf` with these data, the level subgroups being $N\mapsto$ [`NumberField.AdelicLevel.principalLevel`](def/NumberField_PrincipalLevel.html#L17) $(\mathcal{O}_F,F,N)$ (the intersection of `levelOne` at $N$ with its conjugate by the Weyl element) intersected with `finiteAdelicGL2Subgroup F`, the kernel of the archimedean-component map [`NumberField.AdelicLevel.glArch`](def/NumberField_AdelicLevel.html#L191); in these pins the central subgroup is all of $\mathbb{A}_F^\times$, the measures are the adelic Haar measures, and $\nu$ is additive Haar conditioned on $B$. Let $R$ be a smooth cusp realization at these pins of $\Phi$: a function $f$ on $\mathrm{GL}_2(\mathbb{A}_F)$ that is not identically zero, smooth, cuspidal and automorphic with central character `R.centralChar` on the central subgroup, invariant under right translation by the level subgroup at $\Phi.\mathrm{level}$, and, outside a finite exceptional set of places, a Hecke coset eigenfunction with eigenvalue $a_v$ and satisfying the central relation with factor $b_v$. Write $\chi$ for `R.centralChar` transported along the identification of the full subgroup with $\mathbb{A}_F^\times$. Then: (i) $\chi(u)=1$ for every principal idele coming from $u\in F^\times$; (ii) $\chi$ admits $\Phi.\mathrm{level}$ as modulus, i.e. $\chi(u)=1$ for every idele $u$ whose archimedean component is $1$ and whose component at each finite place $v$ has valuation $1$ with $v(u_v-1)\le \exp(-e_v)$, where $e_v$ is the multiplicity of $v$ in $\Phi.\mathrm{level}$; and (iii) if the realization is genuine, that is if $f$ is continuous, then $\chi$ is continuous.
--
--   This is the formal counterpart of the standard fact that the central character of a cuspidal automorphic form on $\mathrm{GL}_2$ over $F$ is a Hecke character of the idele class group whose conductor divides the level, continuous when the form itself is. It is used in the comparison of central characters of realizations agreeing away from a finite set of places, and in the quantitative estimate comparing a realization with sums of its central translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine_principal
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => NumberField.AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        gen B) Φ) :
    IsIdeleClassChar (𝓞 F) F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) ∧
      HeckeCharacter.AdmitsModulus F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Φ.level ∧
      (IsGenuineCuspRealizationAt F
          (productionPinsOf F D (fun N => NumberField.AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            gen B) Φ R →
        Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) := by sorry
