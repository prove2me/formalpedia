-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
-- name    : AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/aa608f20-b2f1-552d-bbba-f6c63e8737cd
-- title:
--   Isotypic cusp space at level bot vanishes
-- statement:
--   Let $F$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $B$ a subset of $\mathbb{A}_F$, and form the carrier data `productionPinsOf F D _ _ B`: the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the window $D$, central group $Z=\top$ (all of $\mathbb{A}_F^\times$), the level family sending an ideal $N$ of $\mathcal{O}_F$ to `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F` (the principal level-$N$ subgroup intersected with the kernel of the archimedean projection `glArch`), the Hecke generators $v\mapsto$ `heckeGen (𝓞 F) F v`, and on $\mathbb{A}_F$ the Borel $\sigma$-algebra with additive Haar measure conditioned on $B$. Let $\xi$ be any homomorphism from this $Z$ to $\mathbb{C}^\times$, let $S$ be a finite set of finite places of $F$, and let $\Psi$ be a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ of complex numbers indexed by finite places). Then the $\mathbb{C}$-span of the functions $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying `IsIsotypicCuspFormAt` for these data at level ideal $\bot$, with exceptional set $S$ and eigensystem $\Psi$, is the zero submodule.
--
--   This is the degenerate case of the isotypic cusp space at the zero level ideal: the Hecke clause of the defining predicate cannot be met there, so the space is zero. It serves as a boundary case for the comparison of isotypic cusp spaces with cuspidal constituents, and is used by the statements relating isotypic spaces, twisted cut traces and cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ = ⊥ := by sorry
