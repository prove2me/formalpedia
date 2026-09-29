-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_principal
-- name    : AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/b243580f-7801-5416-8be9-8350c0215592
-- title:
--   Commutation of two right convolutions at principal level
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb A_F)$, and $N \neq 0$ an ideal of $\mathcal O_F$. For each infinite place $w$ let $\tau_w$ consist of a dimension $n_w$ together with a representation of $\mathrm{rowIsometrySubgroup}_0$ of $F_w$ on $\mathbb C^{n_w}$, and assume each of these representations is irreducible. Write $U$ for the level group attached to $N$ by the production pins over $D$ with levels $N \mapsto \mathrm{principalLevel}(\mathcal O_F,F,N) \sqcap \ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}_v$ and box $\mathrm{adelicBox}$; thus $U$ is the intersection of $\mathrm{levelOne}(N)$ with its conjugate by the Weyl element, cut down to the matrices with trivial archimedean component. Assume $f \colon \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ is level-spherical of the type family with one constituent $\tau_w$ at each place $w$ and level $U$: there is $f_\infty$ on $\mathrm{GL}_2(\mathbb A_{F,\infty})$ given by a smooth compactly supported function of the matrix entries, bi-finite for that type family, invariant under conjugation by each $\mathrm{rowIsometrySubgroup}_0$ at each infinite place, with $f(g) = f_\infty(g_\infty)$ times the indicator of the image of $U$ under the finite-part map, evaluated at $g_f$. Assume $h \colon \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ factorises as an archimedean factor (smooth and compactly supported in the entries) times a locally constant compactly supported factor on the finite part, that $x \mapsto h(x^{-1})$ lies in the archimedean cut submodule of the same type family and $h$ in the dual cut submodule, and that $h(ux) = h(x) = h(xu)$ for all $u \in U$. Then for every continuous $\varphi \colon \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ the two right convolutions against the adelic Haar measure commute: $(\varphi * f) * h = (\varphi * h) * f$, where $(\psi * k)(g) = \int \psi(gx)k(x)\,dx$.
--
--   This is the archimedean–Hecke commutation step for the principal congruence level structure: it says that smoothing by a level-spherical function of a fixed irreducible type at each infinite place commutes with smoothing by any bi-finite, level-bi-invariant factorisable test function. The only ingredient cited is the right invariance of the adelic Haar measure on $\mathrm{GL}_2(\mathbb A_F)$, and the result feeds the extraction of a scalar eigenvalue in [`AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal`](thm.html#AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_principal.lean

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

theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by sorry
