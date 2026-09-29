-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
-- name    : AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/1d5957ce-d8f0-5752-88a5-aa52f0f06c2a
-- title:
--   No Hecke coset eigenfunction at level bot
-- statement:
--   Let $F$ be a number field, $v$ a finite place of $F$ (a height-one prime of $\mathcal{O}_F$), $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ an arbitrary function and $c\in\mathbb{C}$. Take as level group $U =$ `levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F`, the intersection of the preimage under `glFin` of the subgroup of $\mathrm{GL}_2$ of the finite adèles consisting of those $g$ for which both $g$ and $g^{-1}$ satisfy the predicate `IsLevelOneMatrix` at the ideal $\bot$, with the kernel of `glArch`, i.e. the adelic matrices whose archimedean component is trivial. Let $g_v =$ `heckeGen (𝓞 F) F v`, the image of the uniformizer unit at $v$ under `heckeGenAt`. The theorem asserts that the predicate `SmoothCusp.IsHeckeCosetEigenfunctionAt` fails for these data: there is no family $(\mathrm{reps}_i)_{i\in\mathrm{Fin}(N(v)+1)}$, where $N(v) =$ `Ideal.absNorm v.asIdeal`, which is a Hecke coset system for $U$ and $g_v$ — each $\mathrm{reps}_i$ lies in the double coset $U g_v U$, every element of that double coset lies in some coset $\mathrm{reps}_i\,U$, and the $N(v)+1$ cosets $\mathrm{reps}_i\,U$ are pairwise distinct — and which in addition satisfies $\sum_i \varphi(g\,\mathrm{reps}_i) = c\,\varphi(g)$ for all $g$. Since $\varphi$ and $c$ are arbitrary, the obstruction is purely the coset-counting condition.
--
--   This records that the level group attached to the zero ideal is too small for the classical Hecke correspondence at $v$: the double coset of $\mathrm{diag}(\varpi_v,1)$ does not decompose into $N(v)+1$ cosets of this $U$, so no eigenfunction condition of that shape can hold. It is used to show that the isotypic cusp submodule at level $\bot$ vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup.lean

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

theorem AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ c := by sorry
