-- Prove2me | Theorems.Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType_principal
-- name    : AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ffc5b9cd-a30e-54e5-b57e-3ae7ecc5754c
-- title:
--   Hecke coset sums commute with right convolution, principal level
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, $N$ a nonzero ideal of $\mathcal{O}_F$, and `tys` an archimedean type family for $F$ (a count of types at each infinite place together with finite-dimensional representations of the row-isometry subgroups). Write $U$ for the subgroup `(productionPinsOf …).U N`, which by construction of the pins record is $\mathrm{principalLevel}(\mathcal{O}_F,F,N) \sqcap \ker(\mathrm{glArch})$, the pins also recording $D$, the Hecke generators `heckeGen` and the box `adelicBox`. Let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy `IsLevelSphericalOfType F tys U f`: there is $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ which is smooth in the archimedean matrix entries with compact support, bi-finite of type `tys`, invariant under conjugation by row isometries at each infinite place, and such that $f(g) = f_\infty(\mathrm{glArch}\,g)$ times the indicator of the image of $U$ under $\mathrm{glFin}$ at $\mathrm{glFin}\,g$. Let $g \in \ker(\mathrm{glArch})$, let $n \in \mathbb{N}$ and $\mathrm{reps} : \mathrm{Fin}\,n \to \mathrm{GL}_2(\mathbb{A}_F)$ be such that each $\mathrm{reps}\,i$ lies in $UgU$, every element of $UgU$ is of the form $\mathrm{reps}\,i \cdot u$ with $u \in U$, and $(\mathrm{reps}\,i)^{-1}\,\mathrm{reps}\,j \in U$ forces $i = j$. Finally let $\varphi$ be continuous with $\varphi(hu) = \varphi(h)$ for all $h$ and all $u \in U$. Then for all $x$, $\sum_i (\varphi *_{\mathrm{r}} f)(x\,\mathrm{reps}\,i) = \big(\big(\textstyle\sum_i \varphi(\,\cdot\,\mathrm{reps}\,i)\big) *_{\mathrm{r}} f\big)(x)$, where $(\psi *_{\mathrm{r}} f)(y) = \int \psi(yz) f(z)\,dz$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ (the `rightConv` operation).
--
--   The statement says that the smoothing operator given by right convolution against a level-$U$ spherical test function commutes with the Hecke double-coset sum attached to $g$, for the principal congruence level structure $U(N)$ at finite places. It is used in the construction of cuspidal constituents, where [`AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal`](thm.html#AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal) turns such convolutions into scalar multiplications.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hreps : ∀ i, ∃ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
      ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    (fun x => ∑ i, rightConv F φ f (x * reps i)) = rightConv F (fun x => ∑ i, φ (x * reps i)) f := by sorry
