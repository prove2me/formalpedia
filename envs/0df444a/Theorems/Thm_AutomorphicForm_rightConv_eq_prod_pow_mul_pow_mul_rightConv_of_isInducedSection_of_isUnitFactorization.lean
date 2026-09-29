-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
-- name    : AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3b952f9b-dfa6-5f00-98ea-b55984ad2bdf
-- title:
--   Hecke word evaluation on adelic induced sections
-- statement:
--   Let $K$ be a number field and let $S_K$ and $T$ be finite sets of finite places of $K$ with $T$ disjoint from $S_K$. For each finite place $v$ let $\varpi_v$ be an element of the valuation ring of $K_v$, assumed irreducible with nonzero image in $K_v$ for $v \in T$; let $n_v \in \mathbb{N}$ and let $r_v : \mathrm{Fin}(n_v) \to \mathrm{GL}_2(K_v)$ be, for each $v \in T$, a Hecke coset system for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) (the image of $\mathrm{GL}_2(\mathcal{O}_v)$ in $\mathrm{GL}_2(K_v)$) and the element $\mathrm{diag}(\varpi_v,1)$: each $r_v(i)$ lies in the double coset $U\,\mathrm{diag}(\varpi_v,1)\,U$, every element of that double coset lies in some $r_v(i)U$, and $i \mapsto r_v(i)U$ is injective. Let $z_v \in \mathrm{GL}_2(K_v)$ be the scalar matrix $\varpi_v \cdot 1$ for $v \in T$, let $k_v, j_v \in \mathbb{N}$, let $f_\infty$ be a function on $\mathrm{GL}_2(K \otimes \mathbb{R})$ and $f_v$ functions on the $\mathrm{GL}_2(K_v)$. Let $f, f_0 : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support, each admitting a unit factorisation over $S_K \cup T$ (archimedean factor $f_\infty$, a finite factor, local test functions at the places of $S_K \cup T$, the finite factor being the product of the local factors on matrices integral outside $S_K \cup T$ and vanishing otherwise, and $f$ being the product of its archimedean and finite factors) with the same archimedean factor $f_\infty$ and the same local factors $f_v$ at $v \in S_K \setminus T$, while at $v \in T$ the local factor of $f_0$ is the indicator of `localIntegralSet K v` (matrices in $\mathrm{GL}_2(K_v)$ integral together with their inverse) and the local factor of $f$ is the Hecke word $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\mathrm{localIntegralSet}}\Big(\big(r_v(\iota(0))\cdots r_v(\iota(k_v-1))\, z_v^{\,j_v}\big)^{-1}x\Big).$$ Write $\alpha$ for the real-valued character of the idele group obtained from the distributive Haar character of $\mathbb{A}_K$, assumed everywhere positive, let $\mu, \nu : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be characters unramified at every $v \in T$ (trivial on the local units of $\mathcal{O}_v$), let $s \in \mathbb{C}$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, invariant under right translation by `maximalCompactAway K SK` (the adelic maximal compact subgroup intersected with the kernel of the archimedean projection and with the kernels of the components at the places of $S_K$), and an induced section for the pair $(\mu\alpha^{s+1/2}, \nu\alpha^{-(s+1/2)})$, i.e. $\varphi(bg) = \mu\alpha^{s+1/2}(b_{11})\,\nu\alpha^{-(s+1/2)}(b_{22})\,\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup. Then for every $x \in \mathrm{GL}_2(\mathbb{A}_K)$, writing $q_v$ for the absolute norm of $v$, $h_v$ for the adelic Hecke generator `heckeGen` at $v$ and $\ast$ for right convolution against the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, $$(\varphi \ast f)(x) = \prod_{v \in T} \Big(q_v^{1/2}\big(\mu(\det h_v)q_v^{-s} + \nu(\det h_v)q_v^{s}\big)\Big)^{k_v}\Big(q_v^{-1}\big(q_v\,\mu(\det h_v)\,\nu(\det h_v)\big)\Big)^{j_v} \cdot (\varphi \ast f_0)(x).$$
--
--   This is the global form of the computation of the unramified Hecke eigenvalues of the spherical vector in a principal series: replacing the local factor of a test function at $v \in T$ by a word of length $k_v$ in the coset representatives for $\mathrm{GL}_2(\mathcal{O}_v)\,\mathrm{diag}(\varpi_v,1)\,\mathrm{GL}_2(\mathcal{O}_v)$ together with $j_v$ copies of the central element $\varpi_v\cdot 1$ multiplies the convolution of an induced section by the corresponding power of $q_v^{1/2}(\mu(\varpi_v)q_v^{-s} + \nu(\varpi_v)q_v^{s})$ and of $\mu\nu(\varpi_v)$. It is used in the convergence and approximation statements for integrals of the adelic kernel against induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTd : Disjoint T SK)
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hirr : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hcos : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfact : IsUnitFactorization K (SK ∪ T) f faK ff
      (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
        else fSK v))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfact₀ : IsUnitFactorization K (SK ∪ T) f₀ faK ff₀
      (fun v => if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμν : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v)
      (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 K) K
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ)
      (_hφsph : ∀ k ∈ AutomorphicForm.maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
      (x : AdelicGL2 (𝓞 K) K),
    AutomorphicForm.rightConv K φ f x =
      (∏ v ∈ T,
        ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
            (((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ (-s) +
              ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ s)) ^ ks v *
          ((HeckeEigensystem.cNorm v)⁻¹ *
            ((HeckeEigensystem.cNorm v) * ((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ))) ^ js v) *
        AutomorphicForm.rightConv K φ f₀ x := by sorry
