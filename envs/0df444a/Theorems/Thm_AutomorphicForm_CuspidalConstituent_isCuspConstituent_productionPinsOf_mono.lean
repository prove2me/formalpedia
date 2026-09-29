-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono
-- name    : AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/88359a02-b92e-53e9-af98-336ae63fdf87
-- title:
--   Cuspidal constituents pass to smaller windows
-- statement:
--   Let $F$ be a number field, and let $D'\subseteq D$ be subsets of $\mathrm{GL}_2$ of the adèle ring of $F$ and $B$ a subset of that adèle ring. Write $P_D$ for the carrier data `productionPinsOf F D _ _ B`, whose measurable space and measure on $\mathrm{GL}_2(\mathbb{A}_F)$ are the Borel structure and Haar measure `adelicGLHaar`, whose window is $D$, whose central subgroup is the whole unit group $\top$ of $\mathbb{A}_F$, whose level family sends an ideal $N$ of $\mathcal{O}_F$ to $\mathrm{levelOne}(N)$ intersected with the kernel `finiteAdelicGL2Subgroup` of the archimedean projection, whose Hecke elements are `heckeGen` at each finite place, and whose measure on $\mathbb{A}_F$ is `adelicAddHaar` conditioned on $B$; and similarly $P_{D'}$. Since both central subgroups are $\top$, a single character $\xi$ of that subgroup with values in $\mathbb{C}^\times$ serves both. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$. Assume $V$ is a cuspidal constituent for $(P_D,\xi)$, i.e. $V$ lies in `cuspKFiniteSubmodule` for $P_D$ and $\xi$, is stable under right translation by elements of `finiteAdelicGL2Subgroup` and by the archimedean row-isometry elements $\mathrm{rowIsometryInclAt}_0$ at each infinite place, is stable under right convolution with every factorizable test function that is archimedean bi-finite for some archimedean type family, is non-zero, and contains no such submodule other than $0$ and $V$ itself. The conclusion is that $V$ is a cuspidal constituent for $(P_{D'},\xi)$ as well.
--
--   This is one of the window-adaptation steps for the adèlic cuspidal spectrum: the $K$-finite cuspidal space attached to the production data is antitone in the window $D$, because only the integrability condition refers to $D$, while cuspidality, smoothness under the finite level family and the archimedean conditions do not. It is used in the finite-dimensionality statements for the level-invariant and archimedean-cut pieces of a cuspidal constituent, allowing those to be proved for a convenient window and transferred to a general one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono.lean

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

theorem AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono
    (F : Type) [Field F] [NumberField F]
    (D D' : Set (AdelicGL2 (𝓞 F) F)) (hD : D' ⊆ D) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V) :
    IsCuspConstituent F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V := by sorry
