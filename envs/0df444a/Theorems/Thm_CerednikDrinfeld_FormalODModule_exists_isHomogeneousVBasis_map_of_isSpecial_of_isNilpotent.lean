-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/3e00993f-59d8-5ec8-a7e5-11665cc97c67
-- title:
--   Zariski-local homogeneous V-bases for special formal 𝒪_D-modules
-- statement:
--   Let $p$ be a prime and let $B$ be a commutative ring that is an algebra over $\mathbb{Z}_p$. Let $j \colon \mathbb{Z}_{p^2} \to B$ be a ring homomorphism, where $\mathbb{Z}_{p^2}$ is realised as [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field $\mathbb{F}_{p^2}$, and assume that the image of $p$ in $B$ is nilpotent. Let $X$ be a formal $\mathcal{O}_D$-module over $B$, that is, a commutative formal group law $X.F$ of dimension $2$ over $B$ together with an additive and multiplicative action `act` of $\mathbb{Z}_{p^2}$ by endomorphisms of $X.F$ and an endomorphism `varpi` satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ with $\sigma$ the Witt-vector Frobenius. Assume $X$ is special for $j$: the submodules $X.\mathrm{lieZero}\,j$ and $X.\mathrm{lieOne}\,j$ are complementary and each is an invertible $B$-module. Let $x$ be a prime of $B$. Then there is $f \in B$ with $f \notin x$ and a family $\gamma \colon \mathrm{Fin}\,2 \to$ Cartier modules of the base-changed formal group $(X \otimes_B B_f).F$ which is a homogeneous $V$-basis for the composite $B_f$-valued homomorphism $\mathrm{algebraMap} \circ j$: each $\gamma_i$ lies in the graded piece of index $i$, i.e. for every $c \in \mathbb{F}_{p^2}$ the action of the Teichmüller lift of $c$ on $\gamma_i$ is the homothety by $(\mathrm{algebraMap} \circ j)(\tau(c))^{p^i}$, and the $2 \times 2$ matrix of tangent coordinates $(\mathrm{tangent}(\gamma_i)_k)$ has unit determinant in $B_f$.
--
--   This is the statement that a special formal $\mathcal{O}_D$-module over a $p$-nilpotent $\mathbb{Z}_p$-algebra admits, after a Zariski localisation around any given prime of the base, a homogeneous $V$-basis of its Cartier module; such bases are the local frames used in the Cerednik–Drinfeld uniformisation to present the Cartier modules attached to rigidified special formal modules. It feeds the admissibility and period-map results for rigidified triples, where existence of presentations at every prime of the base is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra ℤ_[p] B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B)
    (hX : X.IsSpecial j) (x : PrimeSpectrum B) :
    ∃ f : B, f ∉ x.asIdeal ∧
      ∃ γ : Fin 2 → MvFormalGroup.CartierModule p (X.map (algebraMap B (Localization.Away f))).F,
        (X.map (algebraMap B (Localization.Away f))).IsHomogeneousVBasis
          ((algebraMap B (Localization.Away f)).comp j) γ := by sorry
