-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd
-- name    : AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b6643bde-3c58-5a13-a458-251aac308483
-- title:
--   Vanishing of level-one isotypic cusp spaces at primes dividing the level
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, let $v$ be a finite place of $F$ (a point of the height-one spectrum of $\mathcal{O}_F$), let $Dset$ be an arbitrary subset of $\mathrm{GL}_2$ of the adeles of $F$ and $B$ an arbitrary subset of the adele ring. Consider the carrier data `productionPinsOf F Dset … B`: the Borel structure and Haar measure on adelic $\mathrm{GL}_2$, the domain $Dset$, central subgroup $Z = \top$ (all of $(\mathbb{A}_F)^\times$), the level family sending an ideal $M$ to `levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F`, that is, the matrices over the adeles whose finite part and inverse finite part satisfy the level-one congruence conditions modulo $M$ and whose archimedean part is trivial, the Hecke elements `heckeGen (𝓞 F) F v`, and the Borel structure on the adeles together with the additive Haar measure conditioned on $B$. Let $\xi$ be any homomorphism from $Z$ to $\mathbb{C}^\times$, $N$ an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, and $\Phi$ a Hecke eigensystem over $\mathbb{C}$ (a level, nonzero, together with families $a$, $b$ of complex numbers indexed by the finite places). If $v \notin S$ and the prime of $v$ divides $N$, then the associated isotypic cusp submodule is trivial: the $\mathbb{C}$-span of the functions $\varphi$ on adelic $\mathrm{GL}_2$ that are smooth cuspidal automorphic for these data and $\xi$, continuous, right invariant under the level group at $N$, Hecke coset eigenfunctions with eigenvalue $\Phi.a\,w$ at every $w \notin S$, and satisfy the central relation with eigenvalue $\Phi.b\,w$ at every $w \notin S$, is the zero submodule.
--
--   This is the degenerate case of the isotypic theory: for the level-one congruence family, no nonzero cuspidal Hecke eigenform can have its Hecke eigenvalue condition imposed at a place whose prime divides the level and which is excluded from the exceptional set, so the whole isotypic space collapses. It is used in the derivation of the twisted cut-trace identity over a fundamental domain at a prime, where it disposes of the case in which the prime divides the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ := by sorry
