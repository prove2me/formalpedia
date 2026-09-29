-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds
-- name    : AutomorphicForm.exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/d0dae14e-9eef-590c-9922-1d0ef3bf01d4
-- title:
--   Approximate identity at principal level on GL₂(A_K)
-- statement:
--   Let $K$ be a number field, let $N$ be a nonzero ideal of $\mathcal{O}_K$, and let $U$ be a neighbourhood of the identity in $GL_2(\mathbb{A}_K)$, the group $GL_2$ over the adele ring of $K$. Then there is a function $f : GL_2(\mathbb{A}_K) \to \mathbb{C}$ with the following properties: $f$ is continuous and has compact support; at every point $x$ the value $f(x)$ equals its own real part and that real part is $\ge 0$; the integral of $f$ against the Haar measure `adelicGLHaar` on $GL_2(\mathbb{A}_K)$ (taken with respect to the Borel structure `glBorel`) equals $1$; $f$ is left invariant under every $u$ lying both in `principalLevel (𝓞 K) K N` and in the kernel of the map to $GL_2$ of the infinite adeles, i.e. $f(uy) = f(y)$ for all $y$; for every infinite place $w$ of $K$ and every $k$ in the subgroup `rowIsometrySubgroup₀` of $GL_2(K_w)$, $f$ is invariant under conjugation by the image of $k$ under `rowIsometryInclAt₀ K w`; and finally, whenever $f(x) \ne 0$ one may write $x = a u$ with $a \in U$ having trivial finite-adelic component ($\mathrm{glFin}(a) = 1$) and with $u$ in the intersection of `principalLevel (𝓞 K) K N` with the kernel of the map to $GL_2$ of the infinite adeles. Here `principalLevel (𝓞 K) K N` is the intersection of `levelOne (𝓞 K) K N`, the preimage under `glFin` of the finite-adelic level subgroup `finiteLevelOne`, with the conjugate of that subgroup by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   This is the existence of an approximate identity on $GL_2(\mathbb{A}_K)$ adapted to a principal level structure: a non-negative, compactly supported test function of total mass one which is left invariant under the finite-adelic principal level group, invariant under conjugation by the archimedean row-isometry subgroups, and supported in a product of a prescribed archimedean neighbourhood with the level group. It is used in the approximation argument showing that smooth automorphic functions are dense, namely by [`AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (U : Set (AdelicGL2 (𝓞 K) K)) (hU : U ∈ nhds (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, ((f x).re : ℂ) = f x ∧ 0 ≤ (f x).re) ∧
      (∫ x, f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1) ∧
      (∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ y : AdelicGL2 (𝓞 K) K, f (u * y) = f y) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) ∧
      (∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
        ∃ a u : AdelicGL2 (𝓞 K) K, a ∈ U ∧ glFin (𝓞 K) K a = 1 ∧
          u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * u) := by sorry
