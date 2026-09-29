-- Prove2me | Theorems.Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType
-- name    : AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/cc0f6002-afab-543b-9627-ff5f3cf3fb04
-- title:
--   Hecke coset sums commute with right convolution by spherical f
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, $N \neq 0$ an ideal of $\mathcal{O}_F$ and $\tau$ a family of archimedean types (for each infinite place, a finite list of representations of the row-isometry group of its completion). Form the carrier record `productionPinsOf` from $D$, the level assignment $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, the Hecke generators $v \mapsto \mathrm{heckeGen}(v)$ and the box `adelicBox`; write $U$ for its level group at $N$, namely the elements of $\mathrm{GL}_2(\mathbb{A}_F)$ with trivial archimedean component whose finite component lies in the level-$N$ congruence subgroup. Let $f$ be level-$U$ spherical of type $\tau$: there is $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ which is a smooth compactly supported function of the archimedean matrix entries, lies (together with $x \mapsto f_\infty(x^{-1})$) in the cut submodules attached to $\tau$, is invariant under conjugation by each local row-isometry subgroup, and $f(g) = f_\infty(\mathrm{glArch}\,g)$ times the indicator of the image of $U$ under $\mathrm{glFin}$ at $\mathrm{glFin}\,g$. Let $g$ have trivial archimedean component, and let $\gamma_1,\dots,\gamma_n$ lie in $UgU$, cover $UgU$ by the sets $\gamma_i U$, and satisfy $\gamma_i^{-1}\gamma_j \in U \Rightarrow i=j$. Then for every continuous $\varphi$ with $\varphi(xu)=\varphi(x)$ for all $x$ and all $u \in U$, the functions $x \mapsto \sum_i (\varphi * f)(x\gamma_i)$ and $\bigl(\sum_i \varphi(\,\cdot\,\gamma_i)\bigr) * f$ are equal, where $(\psi * f)(x) = \int \psi(xy) f(y)\,dy$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the statement that the Hecke double-coset sum attached to $g$ at level $U$ commutes with right convolution by a level-$U$ spherical kernel, the finite part of which is the indicator of $U$, the unit of the level-$U$ Hecke algebra. It feeds the construction of the Hecke action on the smoothed cuspidal constituents, being used by [`AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType`](thm.html#AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType) and by [`AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hreps : ∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
      ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    (fun x => ∑ i, rightConv F φ f (x * reps i)) = rightConv F (fun x => ∑ i, φ (x * reps i)) f := by sorry
