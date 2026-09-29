-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
-- name    : AutomorphicForm.exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/cc19ca39-e1a1-5d15-8c1c-bc07144a4336
-- title:
--   Uniform Euler factorisation and decay of Eisenstein Whittaker coefficients
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places, and $\xi_K$ a homomorphism from the full idele group (taken as the top subgroup of $(\mathbb A_K)^\times$) to $\mathbb C^\times$ which is continuous, trivial on the image of $K^\times$, and of modulus $|\xi_K(z)|=\|z\|^{w}$ for a fixed real $w$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character of $\mathbb A_K$. Let $N$ be an ideal of $\mathcal O_K$ each of whose prime divisors lies in $S_K$, $\mathrm{tys}_K$ a family assigning to every infinite place a finite list of representations of the row-isometry subgroup there, $\psi$ an additive character of $\mathbb A_K$ that is continuous, nontrivial and trivial on $K$, $\Omega$ a compact subset of $\mathrm{GL}_2(\mathbb A_K)$, $c'>0$ and $N'\in\mathbb N$. Write $\alpha$ for the idele modulus viewed as a homomorphism into $\mathbb R^\times$, and $\mathrm{hgt}(b)=\alpha(a)/\alpha(d)$ for $b$ in the adelic Borel subgroup (upper triangular, i.e. lower left entry $0$) with diagonal entries $a,d$. The assertion is that there exist a finite set $S\supseteq S_K$ of finite places, $C>0$ and $A\in\mathbb N$ such that the following holds for all data as follows: positivity of $\alpha$; characters $\mu,\nu$ of $(\mathbb A_K)^\times$ which are unitary ($|\mu(x)|=|\nu(x)|=1$), trivial on $K^\times$, continuous, and satisfy $\mu(z)\nu(z)\|z\|^{w}=\xi_K(z)$; real parameters $\tau^\mu_v,\tau^\nu_v$ indexed by the infinite places such that on units of $K_v$ with positive real and vanishing imaginary part the local component of $\mu$ (resp. $\nu$) is $\|\cdot\|^{i\tau^\mu_v}$ (resp. $\|\cdot\|^{i\tau^\nu_v}$), evaluated through the idele norm of the central unit at $v$; integers $m^\mu_v,m^\nu_v$ such that on norm-one units the local component of $\mu$ (resp. $\nu$) is the $m^\mu_v$-th (resp. $m^\nu_v$-th) power of the embedded element; and a family $\psi_s=\psi f(s)$ of functions on $\mathrm{GL}_2(\mathbb A_K)$ such that for every $s$, $\psi_s$ is a section induced from the pair of characters $x\mapsto\mu(x)\alpha(x)^{s+1/2}$ and $x\mapsto\nu(x)\alpha(x)^{-(s+1/2)}$ (so $\psi_s(bg)$ equals the product of these characters evaluated on the two diagonal entries of $b$ times $\psi_s(g)$), each $\psi_s$ is archimedean $K$-finite and smooth for the finite-adelic subgroup, $(s,g)\mapsto\psi_s(g)$ is continuous, $s\mapsto\psi_s(g)$ is differentiable for every $g$, at each infinite place all functions $k\mapsto\psi_s(gk)$ on the row-isometry subgroup lie in one finite-dimensional space $W$ independent of $s$ and $g$, $\psi_s$ is flat ($\psi_s(k)=\psi_0(k)$ for $k$ in the adelic maximal compact subgroup), right invariant under the intersection of the principal level $N$ subgroup with the finite-adelic subgroup, lies in the archimedean cut submodule attached to $\mathrm{tys}_K$, and satisfies $\int_{\mathbf K}\|\psi_0\|^2\le 1$ for the Haar measure on the adelic maximal compact subgroup; together with uniformisers $\varpi_v$ of valuation $-1$ at each finite place. Setting $E(s,h)=\psi_s(h)+\sum_{\xi\in K}\psi_s(w\,u(\xi)h)$ with $w$ the Weyl element and $u(\xi)$ the unipotent matrix with upper right entry $\xi$, there exists $\mathcal V:\{\xi\in K:\xi\neq0\}\to\mathbb C\to\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ such that: (i) $s\mapsto\mathcal V_\xi(s,h)$ is entire for all $\xi,h$; (ii) for $\mathrm{Re}\,s>1$ the Whittaker coefficient of $E(s,\cdot)$ at $\xi$ and $h$, taken with respect to $\psi$ and the production pins (the conditioned additive Haar measure on the adelic box), equals $\prod_{v\notin S}\bigl(1-(\mu\nu^{-1})_v(\varpi_v)\,\mathrm N(v)^{-(2s+1)}\bigr)\cdot\mathcal V_\xi(s,h)$, with $\mathrm N(v)$ the absolute norm of $v$; (iii) for every $h$ and every compact $C_s\subseteq\mathbb C$ there is a summable $u:\{\xi\neq0\}\to\mathbb R$ with $\|\mathcal V_\xi(s,h)\|\le u(\xi)$ for all $\xi$ and all $s\in C_s$; and (iv) for every real $t$, every $b$ in the adelic Borel subgroup and every $\omega\in\Omega$ with $c'\le\mathrm{hgt}(b)$, the family $\xi\mapsto\|\mathcal V_\xi(it,b\omega)\|$ is summable with sum at most $C\bigl(1+\sum_v(|t+\tau^\mu_v|+|t-\tau^\nu_v|+|m^\mu_v|+|m^\nu_v|)\bigr)^{A}\mathrm{hgt}(b)^{-N'}$.
--
--   This is Jacquet's computation of the Whittaker coefficients of $\mathrm{GL}_2$ Eisenstein series in a uniform form: the bad set $S$, the constant $C$ and the exponent $A$ are chosen once for all inducing data of the given level, central character and archimedean types, the normalised coefficients are entire, and the decay in the Borel height on a Siegel-type region is polynomial in the archimedean spectral parameters. It is used in the companion statement comparing the Bruhat-form Eisenstein series with its constant term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.lean

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
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open NumberField
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
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
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (Ω : Set (AdelicGL2 (𝓞 K) K)) (hΩ : IsCompact Ω) (c' : ℝ) (hc' : 0 < c') (N' : ℕ)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ) (A : ℕ), SK ⊆ S ∧ 0 < C ∧
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
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s h =>
      ψf s h + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 K) K) → ℝ := fun b =>
      ((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ 𝒱 : {ξ : K // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 K) K → ℂ,
      (∀ (ξ : {ξ : K // ξ ≠ 0}) (h : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => 𝒱 ξ s h)) ∧
      (∀ (ξ : {ξ : K // ξ ≠ 0}) (s : ℂ) (h : AdelicGL2 (𝓞 K) K), 1 < s.re →
        whittakerCoefficient K (productionPins K) ψ (E s) (ξ : K) h
          = (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒱 ξ s h) ∧
      (∀ (h : AdelicGL2 (𝓞 K) K) (Cs : Set ℂ), IsCompact Cs →
        ∃ u : {ξ : K // ξ ≠ 0} → ℝ, Summable u ∧
          ∀ (ξ : {ξ : K // ξ ≠ 0}), ∀ s ∈ Cs, ‖𝒱 ξ s h‖ ≤ u ξ) ∧
      ∀ (t : ℝ) (b : ↥(adelicBorel (𝓞 K) K)) (ω : AdelicGL2 (𝓞 K) K),
        ω ∈ Ω → c' ≤ hgt b →
          Summable (fun ξ : {ξ : K // ξ ≠ 0} => ‖𝒱 ξ ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω)‖) ∧
          ∑' ξ : {ξ : K // ξ ≠ 0}, ‖𝒱 ξ ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω)‖ ≤
            C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
              (hgt b) ^ (-(N' : ℝ)) := by sorry
