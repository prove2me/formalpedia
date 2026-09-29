-- Prove2me | Theorems.Thm_AutomorphicForm_isLevelSphericalOfType_ofChar_flat
-- name    : AutomorphicForm.isLevelSphericalOfType_ofChar_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/490c2052-b041-53e8-b6c3-fe72d5f107ef
-- title:
--   Flat involution preserves level-spherical functions of unitary character type
-- statement:
--   Let $F$ be a number field, $\sigma$ a real number, $N$ an ideal of $\mathcal O_F$, and let $\chi$ assign to each infinite place $w$ of $F$ a homomorphism $\chi_w$ from the group `rowIsometrySubgroup₀` of $F_w$ to $\mathbb C^\times$, each of which is assumed unitary: $\lVert\chi_w(k)\rVert = 1$ for all $w$ and all $k$. Write $U$ for the subgroup $\mathrm{levelOne}(\mathcal O_F,F,N)$, the preimage under `glFin` of `finiteLevelOne` of level $N$, intersected with the kernel of `glArch`. Let $f : \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ be level-spherical of the type family attached to $\chi$ (one representation at each infinite place, namely the one-dimensional `charRep` of $\chi_w$) at $U$; that is, there is $f_\infty : \mathrm{GL}_2(\mathbb A_{F,\infty}) \to \mathbb C$ which is of the form $\Phi \circ \mathrm{archEntries}$ with $\Phi$ smooth and which has compact support, satisfies the bi-finiteness condition `IsArchFactorBiFinite` for that type family, is invariant under conjugation by each $\mathrm{archRowIsometryInclAt₀}(w,k)$, and factorises $f(g) = f_\infty(\mathrm{glArch}\,g)\cdot \mathbf 1_{\mathrm{glFin}(U)}(\mathrm{glFin}\,g)$. Then the function $\mathrm{flat}(F,\sigma,f)\colon y \mapsto \overline{f(y^{-1})}\,\lVert\det y\rVert_{\mathbb A}^{-\sigma}$ is again level-spherical of the same type at $U$, where $\lVert\cdot\rVert_{\mathbb A}$ is the idele norm.
--
--   The function $f^\flat$ is the kernel representing the adjoint of the right convolution operator $R(f)$ on the cuspidal $L^2$-space, and this statement records that the level-spherical shape of a test function of unitary one-dimensional archimedean type is preserved by that involution. It is used in the analysis of cuspidal constituents, where the convolution operator attached to such an $f$ is compared with its adjoint.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isLevelSphericalOfType_ofChar_flat.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.CuspidalSpectrum

theorem AutomorphicForm.isLevelSphericalOfType_ofChar_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 F)) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ)
      (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f) :
    IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ)
      (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (flat F σ f) := by sorry
