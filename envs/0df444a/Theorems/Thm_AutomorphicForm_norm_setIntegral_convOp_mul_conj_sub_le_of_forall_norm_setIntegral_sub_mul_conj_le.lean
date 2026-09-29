-- Prove2me | Theorems.Thm_AutomorphicForm_norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le
-- name    : AutomorphicForm.norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d5fa4e4b-ea0e-57b9-b3a4-75d5a69dc7d2
-- title:
--   Stability of the R(f)-pairing under weak L² approximation
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, let $SK$ be a finite set of finite places of $K$, let $\xi_K$ be a homomorphism from the full subgroup of the ideles $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is continuous and takes values of absolute value $1$, let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $SK$, and let $tysK$ be an archimedean type family, that is, a finite family $(\rho_{w,i})_{i<\mathrm{card}(w)}$ of representations of the group $\mathrm{rowIsometrySubgroup}_0$ at each infinite place $w$. Write $\Phi_0 =$ `canonicalTruncationDomain K α β` for the subset of $\mathrm{GL}_2(\mathbb{A}_K)$ picked out by a truncation datum for $(\alpha,\beta)$, write $\mu$ for the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$, write $U(M) =$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K` for the principal level subgroup at $M$ intersected with the kernel of the archimedean projection $\mathrm{glArch}$, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support, factorizable (so $f(g) = f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ smooth of compact support through the matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support), satisfying $f(ug)=f(g)=f(gu)$ for all $u \in U(N)$, and archimedean bi-finite for $tysK$ (that is, $x \mapsto f(x^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`, the submodules cut out at each infinite place by the finitely many types $\rho_{w,i}$, respectively their duals). Let $\varepsilon>0$ and let $u_1,u_2,v_1,v_2 : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ all satisfy the predicate `IsAutomorphicFnAt` for the character $\xi_K$ and the carrier data consisting of: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the domain $\Phi_0$, the full central subgroup, the levels $M \mapsto U(M)$, the Hecke generators `heckeGen` at the finite places, and the additive adelic Haar measure conditioned on the adelic box. Assume in addition that $v_1$ and $v_2$ are right $U(N)$-invariant and lie in `archCutSubmodule K tysK`, and that for $m=1,2$ and every $v$ satisfying the same automorphy predicate, right $U(N)$-invariant, lying in `archCutSubmodule K tysK` and with $\|v\|_{L^2(\mu|_{\Phi_0})} \le 1$, one has $\bigl\|\int_{\Phi_0} (u_m - v_m)\,\overline{v}\,d\mu\bigr\| \le \varepsilon$. Then, with $R(f)u =$ `convOp K f u` given by $(R(f)u)(g) = \int u(gx) f(x)\,d\mu(x)$,
--   $$\Bigl\| \int_{\Phi_0} R(f)u_2 \cdot \overline{u_1}\,d\mu - \int_{\Phi_0} R(f)v_2 \cdot \overline{v_1}\,d\mu \Bigr\| \le \Bigl(\int \|f\|\,d\mu\Bigr)\,\varepsilon\,\bigl(\|u_1\|_{L^2(\mu|_{\Phi_0})} + \|u_2\|_{L^2(\mu|_{\Phi_0})} + \varepsilon\bigr),$$
--   the two $L^2$-norms being the real values of the corresponding `eLpNorm`s.
--
--   This is the stability estimate for the truncated pairing $\langle R(f)u_2, u_1\rangle_{\Phi_0}$: replacing the pair $(u_1,u_2)$ by level-$N$ and type-constrained vectors $(v_1,v_2)$ that are $\varepsilon$-close in the weak sense tested against such vectors moves the pairing by at most $\|f\|_1\varepsilon(\|u_1\|_2+\|u_2\|_2+\varepsilon)$. It feeds the density extension of the spectral expansion of $R(f)$, being used in [`AutomorphicForm.forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener`](thm.html#AutomorphicForm.forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hff : IsFactorizableTestFn K f)
    (_hfb : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (_hft : IsArchBiFinite K tysK f)
    (ε : ℝ) (_hε : 0 < ε)
    (u₁ u₂ v₁ v₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hu₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u₁) (_hu₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u₂)
    (_hv₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v₁) (_hv₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v₂) :
    letI := adeleBorel (𝓞 K) K
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v₁ (g * u') = v₁ g) →
      v₁ ∈ archCutSubmodule K tysK →
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v₂ (g * u') = v₂ g) →
      v₂ ∈ archCutSubmodule K tysK →
    (∀ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g) →
        v ∈ archCutSubmodule K tysK →
        eLpNorm v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ 1 →
        ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (u₁ g - v₁ g) * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ ε) →
    (∀ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g) →
        v ∈ archCutSubmodule K tysK →
        eLpNorm v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ 1 →
        ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (u₂ g - v₂ g) * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ ε) →
    ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, convOp K f u₂ g * conj (u₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, convOp K f v₂ g * conj (v₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ≤
      (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ε *
        ((eLpNorm u₁ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))).toReal + (eLpNorm u₂ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))).toReal + ε) := by sorry
