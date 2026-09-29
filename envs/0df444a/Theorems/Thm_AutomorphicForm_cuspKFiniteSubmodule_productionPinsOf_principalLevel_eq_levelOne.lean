-- Prove2me | Theorems.Thm_AutomorphicForm_cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne
-- name    : AutomorphicForm.cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/4c882279-54b4-568d-80c6-27431ba4b5ba
-- title:
--   Principal- and level-one pins give the same K-finite cuspidal space
-- statement:
--   Let $F$ be a number field, let $S$ be a set of adelic points of $\mathrm{GL}_2$ over the adele ring of $\mathcal{O}_F$, and form two carrier pins by `productionPinsOf` from the same data: carrier $S$, the Hecke generators $v \mapsto$ `heckeGen` at each finite place $v$, and the adelic box (the product of the fundamental domain for the lattice of the mixed embedding at the infinite places with the integral finite adeles). Both pins carry the Borel structure and Haar measure on $\mathrm{GL}_2$ of the adeles, centre $\top$, the adelic Borel structure, and the additive adelic Haar measure conditioned on the adelic box; they differ only in the level field, which is $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$ for one and $N \mapsto \mathrm{principalLevel}(N) \sqcap \ker(\mathrm{glArch})$ for the other, where $\mathrm{principalLevel}(N)$ is the intersection of $\mathrm{levelOne}(N)$ with its image under conjugation by the Weyl element. Let $\xi$ be any homomorphism from the centre of the level-one pins (namely the full unit group of the adele ring) to $\mathbb{C}^{\times}$. The assertion is that the two submodules `cuspKFiniteSubmodule` agree: the $\mathbb{C}$-span of the continuous functions $\varphi$ on adelic $\mathrm{GL}_2$ all of whose right translates $x \mapsto \varphi(xg)$ are cuspidal automorphic at the pins with character $\xi$ and $K_f$-smooth, and which lie in the archimedean cut submodule of some archimedean type family, is the same for the principal-level pins as for the level-one pins.
--
--   A compatibility statement in the bookkeeping of adelic cuspidal spaces: the space of $K$-finite smooth cuspidal functions with a given central character depends on the carrier, its measure, the centre and the adelic box, but not on the level structure recorded in the pins. It is used by the transport statement for cuspidal constituents of the isotypic cuspidal submodule at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne
    (F : Type) [Field F] [NumberField F] (S : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ) :
    cuspKFiniteSubmodule F
        (productionPinsOf F S
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ =
      cuspKFiniteSubmodule F
        (productionPinsOf F S
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ := by sorry
