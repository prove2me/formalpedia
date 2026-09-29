-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType
-- name    : AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0420e864-5cf1-5945-89bd-2c21f2eb2b70
-- title:
--   Commuting level-spherical and bi-finite right convolutions on GL₂
-- statement:
--   Let $F$ be a number field, $D$ a subset of $GL_2(\mathbb{A}_F)$, and $N$ a non-zero ideal of $\mathcal{O}_F$; let $U$ denote the level group attached to $N$, namely the subgroup of elements whose finite part lies in the level-$N$ congruence subgroup `finiteLevelOne` intersected with the kernel of the archimedean projection `glArch` (this is the $U$-component of `productionPinsOf` at $N$, the remaining data of that structure — adelic Haar measure on $GL_2$, the set $D$, the full central subgroup, the Hecke generators and the conditioned additive measure on the box — playing no role in the conclusion). At each infinite place $w$ let $\tau_w$ be a finite-dimensional representation of `rowIsometrySubgroup₀` of $F_w$, assumed irreducible. Let $f : GL_2(\mathbb{A}_F) \to \mathbb{C}$ be level-$U$ spherical of the type family having one constituent $\tau_w$ at each $w$: that is, there is $f_\infty$ on $GL_2(F_\infty)$ which is smooth and compactly supported as a function of the matrix entries, archimedean-factor bi-finite of that type, invariant under conjugation by `archRowIsometryInclAt₀` of every element of `rowIsometrySubgroup₀` at every $w$, and $f(g) = f_\infty(\mathrm{glArch}\,g)$ times the indicator of the image of $U$ under `glFin` evaluated at $\mathrm{glFin}\,g$. Let $h : GL_2(\mathbb{A}_F) \to \mathbb{C}$ be a factorizable test function, i.e. $h(g) = h_\infty(\mathrm{glArch}\,g)\,h_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $h_\infty$ an archimedean test factor and $h_{\mathrm{fin}}$ locally constant with compact support, with $h$ archimedean bi-finite of the same type (the function $x \mapsto h(x^{-1})$ lying in `archCutSubmodule` and $h$ in `archDualCutSubmodule`), and bi-invariant under $U$: $h(ux) = h(x)$ and $h(xu) = h(x)$ for all $x$ and all $u \in U$. Then for every continuous $\varphi : GL_2(\mathbb{A}_F) \to \mathbb{C}$ one has $(\varphi * f) * h = (\varphi * h) * f$, where the convolution $\varphi * f$ is the function $g \mapsto \int \varphi(gx) f(x)\,d\mu(x)$ against adelic Haar measure on $GL_2(\mathbb{A}_F)$.
--
--   This is the commutation of the level-$U$ spherical smoothing operator with a right convolution by an arbitrary $U$-bi-invariant, archimedean bi-finite test function, the analytic shadow of multiplicity one for the two-sided $\tau$-cut test algebra at the infinite places. It is used in the eigen-capture step for cuspidal constituents of $GL(2)$, by [`AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType`](thm.html#AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean

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

theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by sorry
