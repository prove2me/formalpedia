-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
-- name    : AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/5d0df8a0-10ca-57ea-9135-21de10876ff4
-- title:
--   Vanishing of the isotypic cusp space when v∣ N
-- statement:
--   Let $F$ be a number field, $v$ a finite prime of $\mathcal{O}_F$, $Dset$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $B$ an arbitrary subset of $\mathbb{A}_F$. Consider the carrier data `productionPinsOf` assembled from these: the Borel measurable structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the set $Dset$, central subgroup $Z=\top$ (all of $\mathbb{A}_F^{\times}$), the level family $N\mapsto \mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, where $\mathrm{principalLevel}(N)$ is the intersection of the level-$N$ congruence subgroup `levelOne` with its conjugate by the Weyl element and $\ker(\mathrm{glArch})$ consists of the adelic matrices trivial at the archimedean places, the Hecke elements $\mathrm{gen}(w)=$ `heckeGen` at each prime $w$, and the Borel structure on $\mathbb{A}_F$ together with the additive Haar measure conditioned on $B$. Let $\xi$ be a homomorphism from this central subgroup to $\mathbb{C}^{\times}$, $N$ an ideal of $\mathcal{O}_F$, $S$ a finite set of finite primes, and $\Phi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a_w$, $b_w$). Assume $v\notin S$ and that $v$ divides $N$. Then `isotypicCuspSubmodule`, the $\mathbb{C}$-span of those $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ that are smooth cuspidal automorphic for these data and $\xi$, continuous, right invariant under the level-$N$ group, Hecke coset eigenfunctions with eigenvalue $\Phi.a\,w$ at every $w\notin S$, and satisfy $\varphi(\mathrm{centralScalar}(\det \mathrm{gen}(w))g)=\Phi.b\,w\cdot\varphi(g)$ for $w\notin S$, is the zero submodule.
--
--   This records the incompatibility, at the principal congruence levels, between the coset-theoretic Hecke eigenfunction condition at a prime $v$ and $v$ dividing the level: no nonzero form can be an eigenfunction in this sense at a prime outside $S$ dividing $N$. It is used in the downstream results on existence of nonzero isotypic forms and on factorisable vectors, where it forces the relevant levels to be prime to the primes at which Hecke operators are taken.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ := by sorry
