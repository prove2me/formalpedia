-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
-- name    : AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/195900b3-4b3e-57e9-ac7b-e752d1a481bd
-- title:
--   Hecke-word eigenvalue for adelic induced sections under right convolution
-- statement:
--   Let $L/K$ be an extension of number fields, let $S,T$ be finite sets of nonzero primes of $\mathcal O_K$ with $T$ disjoint from $S$, and let $S_L$ be a finite set of primes of $\mathcal O_L$ none of whose members lies above a prime of $T$. For each prime $v$ of $\mathcal O_K$ fix an extension $w_v$ of $v$ to $\mathcal O_L$ and an element $\varpi_v$ of the valuation ring of $L_{w_v}$, irreducible and with nonzero image in $L_{w_v}$ for $v\in T$; fix $n_v\in\mathbb N$ and $r_{v,0},\dots,r_{v,n_v-1}\in\mathrm{GL}_2(L_{w_v})$ which for $v\in T$ form a Hecke coset system for the subgroup $\mathrm{GL}_2$ of the valuation ring inside $\mathrm{GL}_2(L_{w_v})$ and the element $\mathrm{diag}(\varpi_v,1)$ (each representative lies in the double coset, the classes of the representatives in the quotient by the subgroup cover the double coset, and the map to that quotient is injective); fix $z_v\in\mathrm{GL}_2(L_{w_v})$ equal, for $v\in T$, to the scalar matrix $\varpi_v\cdot 1$; and fix exponents $k_v,j_v\in\mathbb N$. Let $\varphi_a$ be a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S(v)$ functions on $\mathrm{GL}_2(L\otimes_K K_v)$. Let $\varphi$ be continuous with compact support on $\mathrm{GL}_2(\mathbb A_L)$ and $\varphi_f$ a function on $\mathrm{GL}_2$ of the finite adeles such that `IsSemiLocalFactorization` holds for $S\cup T$ with archimedean factor $\varphi_a$, finite factor $\varphi_f$ and semi-local factors equal to $\varphi_S(v)$ for $v\notin T$ and, for $v\in T$, to $x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\mathrm{int}}\big(c_v(\iota)^{-1}x\big)$, where $\mathbf 1_{\mathrm{int}}$ is the indicator of the semi-local integral units set and $c_v(\iota)$ is the semi-local component at $v$ of the image under the embedding at $w_v$ of $\big(\prod_m r_{v,\iota(m)}\big)z_v^{\,j_v}$; let $\varphi_0,\varphi_{f,0}$ satisfy the same factorisation hypothesis with the same $\varphi_a$ and $\varphi_S$, the factor at $v\in T$ being the indicator of the semi-local integral units set. Write $\alpha$ for the module character of $\mathbb A_L$ given by `distribHaarChar` viewed as a homomorphism to $\mathbb R^\times$; assume $\alpha$ is positive, let $\mu,\nu:\mathbb A_L^\times\to\mathbb C^\times$ be characters unramified at each $w_v$, $v\in T$, let $s\in\mathbb C$, and let $\psi$ on $\mathrm{GL}_2(\mathbb A_L)$ be continuous, satisfy $\psi(bg)=\mu\alpha^{s+1/2}(b_{11})\,\nu\alpha^{-(s+1/2)}(b_{22})\,\psi(g)$ for all $b$ in the adelic Borel subgroup, and be right invariant under `maximalCompactAway L SL` (elements of the adelic maximal compact with trivial archimedean component and trivial components at the primes in $S_L$). Then for every $x\in\mathrm{GL}_2(\mathbb A_L)$ the right convolution $\int\psi(x y)\varphi(y)\,dy$ against the adelic Haar measure equals $$\prod_{v\in T}\Big(N(w_v)^{1/2}\big(\mu(\det h_{w_v})N(w_v)^{-s}+\nu(\det h_{w_v})N(w_v)^{s}\big)\Big)^{k_v}\Big(N(w_v)^{-1}\big(N(w_v)\,\mu(\det h_{w_v})\,\nu(\det h_{w_v})\big)\Big)^{j_v}$$ times $\int\psi(xy)\varphi_0(y)\,dy$, where $N(w_v)$ is the absolute norm of $w_v$ and $h_{w_v}=$ `heckeGen (𝓞 L) L (ws v).1` is the adelic element with uniformiser entry at $w_v$.
--
--   This is the global form of the statement that a spherical vector in the principal series induced from $(\mu|\cdot|^{s+1/2},\nu|\cdot|^{-(s+1/2)})$ is a simultaneous eigenvector for the Hecke operators and the central translations at the chosen places above $T$, the eigenvalues being $N(w)^{1/2}(\mu(\varpi)N(w)^{-s}+\nu(\varpi)N(w)^{s})$ and $\mu\nu(\varpi)$; the Hecke word is encoded here in the semi-local test factor of $\varphi$ at the places of $T$, and the comparison is with the corresponding convolution against the spherical test function $\varphi_0$. It is used in the construction of atomic families of automorphic forms with prescribed Hecke eigenvalues over the extension $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTd : Disjoint T S)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hirr : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T,
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hcos : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfact : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
    (φ₀ : AdelicGL2 (𝓞 L) L → ℂ) (hφ₀ : Continuous φ₀) (hφ₀c : HasCompactSupport φ₀)
    (φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfact₀ : IsSemiLocalFactorization K L (S ∪ T) φ₀ φa φf₀
      (fun v => if v ∈ T then (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) else φS v)) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμν : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt μ (ws v).1 ∧
        NumberField.TateGlobal.IsUnramifiedCharAt ν (ws v).1)
      (s : ℂ) (ψ : AdelicGL2 (𝓞 L) L → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 L) L
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) ψ)
      (_hψc : Continuous ψ)
      (_hψsph : ∀ k ∈ AutomorphicForm.maximalCompactAway L SL, ∀ g : AdelicGL2 (𝓞 L) L, ψ (g * k) = ψ g)
      (x : AdelicGL2 (𝓞 L) L),
    AutomorphicForm.rightConv L ψ φ x =
      (∏ v ∈ T,
        ((HeckeEigensystem.cNorm (ws v).1) ^ ((1 / 2 : ℝ) : ℂ) *
            (((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ (-s) +
              ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ s)) ^ ks v *
          ((HeckeEigensystem.cNorm (ws v).1)⁻¹ *
            ((HeckeEigensystem.cNorm (ws v).1) *
              ((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
              ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ))) ^ js v) *
        AutomorphicForm.rightConv L ψ φ₀ x := by sorry
