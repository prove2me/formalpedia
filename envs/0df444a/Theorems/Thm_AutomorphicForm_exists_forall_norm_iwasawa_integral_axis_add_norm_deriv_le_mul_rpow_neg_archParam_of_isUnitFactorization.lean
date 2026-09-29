-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
-- name    : AutomorphicForm.exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/668d35ed-ede7-5d7c-b971-71748816a860
-- title:
--   Uniform rapid decay of the Iwasawa integral along the unitary axis
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places, and $\xi_K$ a continuous character of the full idele unit group of $K$ which is trivial on the image of $K^\times$ and satisfies $|\xi_K(z)| = \|z\|^w$ for a fixed real $w$, where $\|\cdot\|$ denotes the module of the adele ring. Let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ be an archimedean type family, and let $f_0$ be a continuous compactly supported function on $\mathrm{GL}_2$ of the adeles admitting a unit factorisation with archimedean factor $f_{a,K}$, finite factor $f_{f,K}$ and local factors $f_{S_K}$: $f_{a,K}$ is smooth in the matrix-entry coordinates of the mixed space and compactly supported, $f_{f,K}$ and each $f_{S_K}(v)$ for $v \in S_K$ are locally constant with compact support, $f_{f,K}(h)$ equals $\prod_{v \in S_K} f_{S_K}(v)(h_v)$ when $h_v$ is integral for all $v \notin S_K$ and vanishes otherwise, and $f_0(g) = f_{a,K}(g_\infty) f_{f,K}(g_{\mathrm{fin}})$. Let $N'$ be a natural number and write $\alpha$ for the module $x \mapsto \|x\|$ viewed as a homomorphism to $\mathbb{R}^\times$. Then there is a constant $C > 0$, depending only on these data, such that the following holds for every choice of the remaining data: positivity of $\alpha$; unitary characters $\mu, \nu$ of the idele unit group, continuous, trivial on principal ideles, with $\mu(z)\nu(z)\|z\|^{w} = \xi_K(z)$; real parameters $\tau_\mu(v), \tau_\nu(v)$ for each infinite place $v$ such that on the units of $K_v$ with positive real and vanishing imaginary embedding the local components of $\mu$ and $\nu$ are $\|\cdot\|^{i\tau_\mu(v)}$ and $\|\cdot\|^{i\tau_\nu(v)}$; and two families $\varphi_s, \psi_s$ of functions on $\mathrm{GL}_2$ of the adeles, each of which, for every $s$, transforms under the adelic Borel subgroup by $(\mu\|\cdot\|^{s+1/2}) \otimes (\nu\|\cdot\|^{-(s+1/2)})$ applied to the two diagonal entries, is archimedean $K$-finite, is smooth for the finite adelic subgroup, lies in the $\mathrm{tys}_K$-isotypic submodule and is right invariant under the intersection of the principal level of $N$ with the finite adelic subgroup; jointly continuous in $(s,g)$ and holomorphic in $s$; $K$-finite uniformly in $s$ and $g$ at each infinite place (the right translates along the archimedean row-isometry subgroup lie in one finite-dimensional space); flat on the maximal compact subgroup, i.e. $\varphi_s = \varphi_0$ and $\psi_s = \psi_0$ there; and $L^2$-normalised, $\int_{\mathbf{K}} |\varphi_0|^2 \le 1$ and $\int_{\mathbf{K}} |\psi_0|^2 \le 1$ against the Haar measure of the maximal compact subgroup. Setting $$a(t) = \int_{\mathbf{K}} \int_{\mathbb{A}} \int \int \int_{\mathbf{K}} \mu(ut')\|ut'\|^{it+1/2}\, \nu(u)\|u\|^{-(it+1/2)}\, \|\det(z(u)a(t'))\|^{w/2}\, \|t'\|^{-1}\, f_0\bigl(k^{-1} n(x) z(u) a(t') k'\bigr)\, \psi_0(k')\, \overline{\varphi_0(k)}\, dk'\, d^\times t'\, d^\times u\, dx\, dk,$$ the inner integrals being taken against the Haar measure of the maximal compact subgroup, the Haar measure of the idele unit group twice, additive adelic Haar measure, and again the maximal compact Haar measure, where $n(x)$ is the upper unipotent matrix with entry $x$, $z(u)$ the central scalar $u$ and $a(t')$ the diagonal matrix $\mathrm{diag}(t',1)$, and setting $D(t) = \sum_{v \mid \infty} (|t + \tau_\mu(v)| + |t - \tau_\nu(v)|)$, there is a function $a' : \mathbb{R} \to \mathbb{C}$ which is the derivative of $a$ at every point, is continuous, and satisfies $\|a(t)\| + \|a'(t)\| \le C (1 + D(t))^{-N'}$ for all real $t$.
--
--   This is the analytic estimate underlying the rapid decay, in the unitary parameter $t$, of the matrix coefficient attached to a pair of flat holomorphic families of induced sections against a factorisable test function: the $t$-dependence enters only through the character $\|\cdot\|^{it}$ on the split torus, so that the Iwasawa integral is a Fourier transform in the torus coordinates of a compactly supported smooth function, and one obtains a bound of order $(1 + D(t))^{-N'}$ for every $N'$, with a constant uniform in the admissible pairs $(\mu,\nu)$ and in the families $\varphi, \psi$. It is used by [`AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization), where the Iwasawa integral is identified with the matrix coefficient up to a positive constant depending only on $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (_hfact : IsUnitFactorization K SK f₀ faK ff₀ fSK)
    (N' : ℕ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ C : ℝ, 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfK : ∀ s, IsArchKFinite K (φf s)) (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hφff : ∀ s, IsKfSmooth K (φf s)) (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g)) (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hφfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => φf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf s (g * u) = φf s g)
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule K tysK) (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hφfn : ∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1),
    let a : ℝ → ℂ := fun t => ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K)
    let D : ℝ → ℝ := fun t => ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)
    ∃ a' : ℝ → ℂ, (∀ t : ℝ, HasDerivAt a (a' t) t) ∧ Continuous a' ∧
      ∀ t : ℝ, ‖a t‖ + ‖a' t‖ ≤ C * (1 + D t) ^ (-(N' : ℝ)) := by sorry
