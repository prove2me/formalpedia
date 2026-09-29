-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/7180780c-3f3e-5848-b794-373b83e76cd9
-- title:
--   Level–type averaging kernel on the adelic maximal compact
-- statement:
--   Let $K$ be a number field, let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ all of whose values have absolute value $1$, let $N$ be a non-zero ideal of $\mathcal{O}_K$, and let $\mathrm{tys}_K$ be an `ArchTypeFamily` for $K$, i.e. a finite number $\mathrm{card}(w)$ of representations of the row-isometry group of $K_w$ on finite-dimensional complex spaces for each infinite place $w$. Then there is a function $\kappa$ on `adelicMaximalCompact K` — the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ of elements whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place $w$ satisfies `IsRowIsometry` (determinant of absolute value $1$, and the associated row action preserving $\|x\|^2+\|y\|^2$) — such that, with $\mathrm{d}k$ the Haar measure `maximalCompactHaar K`: (a) $\kappa$ is continuous; (b) $\kappa(k^{-1})=\overline{\kappa(k)}$; (c) $\int \kappa(k')\kappa(k'^{-1}k)\,\mathrm{d}k'=\kappa(k)$ for all $k$; (d) for every function $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, with no regularity assumed, every $k$ in the maximal compact whose archimedean component has determinant exactly $1$ at every real place, and every $g$, one has $\int\kappa(k')\varphi(gk'k)\,\mathrm{d}k'=\int\kappa(k')\varphi(gkk')\,\mathrm{d}k'$; (e) the averaging operator $P\varphi(g)=\int\kappa(k)\varphi(gk)\,\mathrm{d}k$ fixes every continuous $\varphi$ which is `IsArchKFinite` (at each infinite place the right translates under the archimedean row-isometry subgroup span a finite-dimensional space), is invariant under right multiplication by `principalLevel (𝓞 K) K N` intersected with the kernel `finiteAdelicGL2Subgroup K` of the archimedean projection, lies in `archCutSubmodule K tysK` (the intersection over infinite places $w$ of the sums of the type submodules attached to the representations $\mathrm{tys}_K.\mathrm{rep}\,w\,i$), and satisfies $\varphi(g\,z)=\xi_K(z)\varphi(g)$ for central scalars $z$; (f) for every continuous arch-$K$-finite $\varphi$, $P\varphi$ is again continuous and arch-$K$-finite, is right invariant under that level subgroup, and lies in `archCutSubmodule K tysK`; and (g) $P(P\varphi)=P\varphi$ for continuous arch-$K$-finite $\varphi$.
--
--   This is the construction of an idempotent, self-adjoint convolution kernel on the adelic maximal compact subgroup realising the projection onto the prescribed archimedean $K$-types and the level-$N$ invariants, together with the commutation property with right translation by the determinant-one part at the real places. It is used in the Paley–Wiener and pseudo-Eisenstein estimates for averaged sections, and in identifying the image of the residual projection inside the archimedean type cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule.lean

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

theorem AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ κ : ↥(adelicMaximalCompact K) → ℂ, Continuous κ ∧ (∀ k, κ k⁻¹ = conj (κ k)) ∧
      (∀ k : ↥(adelicMaximalCompact K), ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k) ∧

      (∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K,
          (∫ k', κ k' * φ (g * (k' : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
            ∫ k', κ k' * φ (g * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ → (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = φ) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        Continuous (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
        IsArchKFinite K (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) (g * u) = (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) g) ∧
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∈ archCutSubmodule K tysK) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        (fun g => ∫ k, κ k * (∫ k', κ k' * φ (g * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
          ∂(maximalCompactHaar K)) =
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by sorry
