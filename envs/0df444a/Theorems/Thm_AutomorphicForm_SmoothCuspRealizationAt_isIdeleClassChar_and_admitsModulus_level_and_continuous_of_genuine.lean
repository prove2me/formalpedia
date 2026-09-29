-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
-- name    : AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/78af7fc8-47c5-54e8-b41f-89adb6ebce26
-- title:
--   Central character: idele class character admitting the level as modulus
-- statement:
--   Let $F$ be a number field, let $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be a set, let $\mathrm{gen}$ assign to each finite place of $F$ an element of $\mathrm{GL}_2(\mathbb{A}_F)$, let $B \subseteq \mathbb{A}_F$ be a set, and let $\Phi$ be a Hecke eigensystem over $F$ with complex coefficients, consisting of a nonzero ideal $\Phi.\mathrm{level} \subseteq \mathcal{O}_F$ and two families of complex numbers indexed by the finite places. Consider the carrier data `productionPinsOf` built from $D$, $\mathrm{gen}$, $B$ and the level subgroups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, i.e. the Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the full central subgroup $Z = \top \le \mathbb{A}_F^\times$, and the adelic Haar measure conditioned on $B$. Let $R$ be a smooth cusp realization at these data for $\Phi$: a nowhere-identically-zero function on $\mathrm{GL}_2(\mathbb{A}_F)$ with a central character on $Z$, satisfying the smooth cuspidality condition, invariance under right translation by the level subgroup attached to $\Phi.\mathrm{level}$, and the Hecke and central eigenvalue identities outside a finite exceptional set. Write $\mu_R : \mathbb{A}_F^\times \to \mathbb{C}^\times$ for the central character of $R$ composed with the identification of $\mathbb{A}_F^\times$ with $\top$. Then: (1) $\mu_R$ kills the principal ideles, i.e. $\mu_R(u) = 1$ for every $u \in F^\times$ mapped diagonally into $\mathbb{A}_F^\times$; (2) $\mu_R$ admits $\Phi.\mathrm{level}$ as a modulus, i.e. $\mu_R(u) = 1$ for every idele $u$ whose archimedean component is $1$ and whose component at each finite place $v$ has valuation $1$ and satisfies $v(u_v - 1) \le \exp(-e_v)$, where $e_v$ is the exponent of $v$ in $\Phi.\mathrm{level}$; and (3) if $R$ is genuine, that is if its underlying function on $\mathrm{GL}_2(\mathbb{A}_F)$ is continuous, then $\mu_R$ is continuous.
--
--   This records the standard properties of the central character of an automorphic form on $\mathrm{GL}_2$ over a number field: it descends to the idele class group, has conductor dividing the level, and is continuous once the form is. It is used downstream in the Rankin–Selberg analysis of the realizations, where the characterisation of idele class characters and the comparison of $|\mu_R|$ with powers of the idelic norm require exactly these three inputs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        gen B) Φ) :
    IsIdeleClassChar (𝓞 F) F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) ∧
      HeckeCharacter.AdmitsModulus F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Φ.level ∧
      (IsGenuineCuspRealizationAt F
          (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            gen B) Φ R →
        Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) := by sorry
