-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
-- name    : AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e9439786-f1a5-53f6-a2f6-4c1093add84c
-- title:
--   Uniform rapid decay of K-matrix coefficients on the unitary axis
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places, and $\xi_K$ a continuous character of the full idele unit group which is trivial on the principal ideles and whose modulus is $\|\cdot\|^{w}$ for a real $w$, where $\|\cdot\|$ is the idele norm given by the module character of the adele ring. Let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ be a family of archimedean types (finitely many representations of the row-isometry group at each infinite place), and let $f_0$ be a continuous compactly supported function on $\mathrm{GL}_2(\mathbb{A}_K)$ admitting a unit factorisation over $S_K$ with archimedean factor $f_a$, finite factor $f_f$ and local factors $f_v$. Write $\alpha_m$ for the real-valued character $x\mapsto\|x\|$. Then for every $N'\in\mathbb{N}$ there is a constant $C>0$, depending only on the data above, such that the following holds for all further data: any continuous characters $\mu,\nu$ of the idele unit group that are unitary (of absolute value $1$ everywhere) and trivial on principal ideles, with $\mu(z)\nu(z)\|z\|^{w}=\xi_K(z)$; any $\tau^\mu,\tau^\nu:\{v\mid\infty\}\to\mathbb{R}$ such that for each infinite place $v$ and each unit $x$ of $K_v$ whose image under the extension embedding is a positive real, $\mu_v(x)=\|x\|^{i\tau^\mu_v}$ and $\nu_v(x)=\|x\|^{i\tau^\nu_v}$, where $\mu_v,\nu_v$ are the restrictions of $\mu,\nu$ along the central embedding of $K_v^\times$; and any two families $\varphi,\psi:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ subject to the following conditions, summarised here: each $\varphi_s,\psi_s$ transforms under the adelic Borel subgroup by $\varphi_s(bg)=\mu\alpha_m^{s+1/2}(b_{11})\,\nu\alpha_m^{-(s+1/2)}(b_{22})\varphi_s(g)$; each $\varphi_s,\psi_s$ is archimedean $K$-finite at every infinite place and has open stabiliser in the finite-adelic subgroup; the maps $(s,g)\mapsto\varphi_s(g)$, $(s,g)\mapsto\psi_s(g)$ are continuous and holomorphic in $s$ for fixed $g$; at each infinite place all right translates $k\mapsto\varphi_s(gk)$ along the row-isometry subgroup lie in one fixed finite-dimensional space of functions, uniformly in $s$ and $g$, and likewise for $\psi$; the families are flat, $\varphi_s=\varphi_0$ and $\psi_s=\psi_0$ on the adelic maximal compact subgroup; they are right invariant under the intersection of the principal level $N$ with the finite-adelic subgroup; each $\varphi_s,\psi_s$ lies in the submodule cut out by $\mathrm{tys}_K$; and $\int_{\mathbf{K}}|\varphi_0|^2\le 1$, $\int_{\mathbf{K}}|\psi_0|^2\le 1$ against the Haar measure of the maximal compact. For such data set $$a(t)=\int_{\mathbf{K}}\bigl(R(f_0)(\psi_{it}\|\det\|^{w/2})\bigr)(k)\,\overline{\varphi_{it}(k)}\,dk,\qquad R(f_0)h(g)=\int h(gx)f_0(x)\,dx,$$ and $D(t)=\sum_{v\mid\infty}(|t+\tau^\mu_v|+|t-\tau^\nu_v|)$. The conclusion is that there is a continuous $a':\mathbb{R}\to\mathbb{C}$ with $a'(t)$ the derivative of $a$ at every $t$, and $\|a(t)\|+\|a'(t)\|\le C\,(1+D(t))^{-N'}$ for all real $t$.
--
--   This is the coefficient-decay estimate for flat holomorphic families of principal-series sections along the unitary axis, with a constant uniform in the inducing unitary characters $\mu,\nu$ of fixed product $\xi_K\|\cdot\|^{-w}$. It is obtained by rewriting the $\mathbf{K}$-pairing of the right convolution as an Iwasawa integral and applying the corresponding decay bound for that integral, and it feeds the construction of a summable dominant for the continuous-spectrum contribution as well as the variant stated for factorisable test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
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
    let a : ℝ → ℂ := fun t =>
      ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
        conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    let D : ℝ → ℝ := fun t => ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)
    ∃ a' : ℝ → ℂ, (∀ t : ℝ, HasDerivAt a (a' t) t) ∧ Continuous a' ∧
      ∀ t : ℝ, ‖a t‖ + ‖a' t‖ ≤ C * (1 + D t) ^ (-(N' : ℝ)) := by sorry
