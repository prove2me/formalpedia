-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat
-- name    : AutomorphicForm.exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/823de394-45f5-51b0-a1c8-703bd80fd7e5
-- title:
--   Uniform Whittaker factorisation for flat level-N Eisenstein pieces
-- statement:
--   **Fixed data.** Let $K$ be a number field (with decidable equality on its finite places and a Borel measurable structure on the idele units), $S_K$ a finite set of finite places of $K$, and $\xi_K$ a homomorphism from the full group of ideles (presented as the top subgroup of $(\mathbb{A}_K)^\times$) to $\mathbb{C}^\times$. The hypothesis `hξc` asks that $z\mapsto\xi_K(z)$ be continuous, `hξt` that $\xi_K$ be trivial on the image of $K^\times$, and `hξw` that $\|\xi_K(z)\|=\|z\|^{w}$ for a fixed real exponent $w$, where $\|\cdot\|$ denotes [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), i.e. the module $\mathrm{distribHaarChar}$ of the adele ring. Let $N$ be an ideal of $\mathcal{O}_K$ with `hN`: every finite place dividing $N$ lies in $S_K$. Let `tysK` be an `ArchTypeFamily K`, that is, for each infinite place $v$ a number $\mathrm{card}(v)$ of prescribed representations of the row-isometry subgroup of $\mathrm{GL}_2(K_v)$.
--
--   **The additive character.** $\psi$ is an additive character of $\mathbb{A}_K$ with `_hψ` asserting `IsGlobalAddChar`, i.e. $\psi$ is trivial on $K$, continuous and non-trivial. Its local data are given by characters $\psi_v$ of the completions $K_v$ at the finite places and integers $n_{\psi}(v)$ of finite support, subject to: $\psi_v$ is trivial on $\{x:\ |x|_v\le q^{\,n_\psi(v)}\}$ (`_hψv`), $\psi_v$ is non-trivial somewhere in the next larger ball (`_hψv'`, exactness of the level), and $\psi$ restricted to the finite adeles is the finitely-supported product of the $\psi_v$ (`_hψfin`). At the infinite places, non-zero frequencies $\theta_r(i)\in\mathbb{R}$ at the real places and $\theta_c(v)\in\mathbb{C}$ at the complex places are given (`_hθr`, `_hθc`), and `_hψarch` prescribes the archimedean component of $\psi$ on the mixed space as $\prod_i e^{-2\pi i\,\theta_r(i)p_i}\cdot\prod_v e^{-4\pi i\,\mathrm{Re}(\theta_c(v)p_v)}$. Finally, two reals $\sigma_1,\sigma_2$ fix a vertical strip.
--
--   Throughout, $\alpha_m$ denotes the real-unit-valued character $z\mapsto\|z\|$ obtained from $\mathrm{distribHaarChar}$ of $\mathbb{A}_K$, and the adele ring carries its Borel $\sigma$-algebra.
--
--   **Uniform constants.** The assertion is that there exist a finite set $S$ of finite places with $S_K\subseteq S$, natural numbers $n_0,k_0,\kappa$, an integer $t_0$, and reals $C_0,M\ge 0$, depending only on the data above, such that the following holds for all further data.
--
--   **Data quantified over (after the constants).** Positivity of $\alpha_m$ (`hαm`); a pair of characters $\mu,\nu$ of $(\mathbb{A}_K)^\times$ which are unitary ($|\mu(x)|=|\nu(x)|=1$), idele class characters (trivial on $K^\times$), continuous, and satisfy $\mu(z)\nu(z)\|z\|^{w}=\xi_K(z)$ (`_hμν`); archimedean exponents $\tau_\mu,\tau_\nu:\{\text{infinite places}\}\to\mathbb{R}$ such that on units of $K_v$ whose embedding is a positive real number one has $\mu_v(x)=\|x\|^{i\tau_\mu(v)}$, respectively $\nu_v(x)=\|x\|^{i\tau_\nu(v)}$, where $\mu_v,\nu_v$ are the local characters [`NumberField.TateGlobal.archLocalChar`](def/NumberField_TateGlobalZeta.html#L55) obtained by restricting along `archUnitHom` (`_hτμ`, `_hτν`); weights $m_\mu,m_\nu:\{\text{infinite places}\}\to\mathbb{Z}$ such that on elements of norm $1$ one has $\mu_v(x)=x^{m_\mu(v)}$, respectively $\nu_v(x)=x^{m_\nu(v)}$ (`_hmμ`, `_hmν`).
--
--   Next, a family $\psi_f:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ subject to the following hypotheses. For each $s$, $\psi_f(s,\cdot)$ is an induced section for the pair $(\mu\cdot\|\cdot\|^{s+1/2},\ \nu\cdot\|\cdot\|^{-(s+1/2)})$ (`etaFst`, `etaSnd` built from `cpowChar`), i.e. $\psi_f(s,bg)=\chi_1(b_{11})\chi_2(b_{22})\psi_f(s,g)$ for $b$ in the adelic Borel subgroup (`_hψf`); $\psi_f(s,\cdot)$ is archimedean $K$-finite, meaning at each infinite place the right translates under the archimedean row-isometry subgroup span a finite-dimensional space (`_hψfK`); $\psi_f(s,\cdot)$ is $K_f$-smooth, i.e. its stabiliser under right translation inside the subgroup of matrices with trivial archimedean part is open (`_hψff`); $\psi_f$ is jointly continuous (`_hψfjc`) and holomorphic in $s$ for each $g$ (`_hψfhol`); at each infinite place $v$ there is a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup containing all the functions $k\mapsto\psi_f(s,gk)$ (`_hψfKu`); flatness: $\psi_f(s,k)=\psi_f(0,k)$ for every $k$ in the adelic maximal compact subgroup (finite part integral, archimedean parts row isometries) (`_hψfflat`); right invariance under $\mathrm{principalLevel}(N)\cap\{\text{trivial archimedean part}\}$, where $\mathrm{principalLevel}(N)$ is the intersection of $\mathrm{levelOne}(N)$ with its conjugate by the Weyl element (`_hψflev`); membership $\psi_f(s,\cdot)\in\mathrm{archCutSubmodule}(\mathtt{tysK})$, i.e. at every infinite place the function lies in the span of the type subspaces listed by the family (`_hψfty`); and the normalisation $\int_{\mathbf{K}}\|\psi_f(0,k)\|^2\,d k\le 1$ for the Haar measure on the adelic maximal compact subgroup (`_hψfn`). Finally, uniformisers $\varpi_v$ at all finite places, with $|\varpi_v|_v=q_v^{-1}$ (`_hϖ`).
--
--   **Auxiliary objects.** $E(s,h)=\psi_f(s,h)+\sum_{\xi\in K}\psi_f\bigl(s,\ w_0\,u(\xi)\,h\bigr)$ is the Bruhat-form Eisenstein series, $w_0$ being the global Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $u(\xi)$ the unipotent matrix with upper-right entry $\xi$. The archimedean integrals are
--   $$j_{\mathbb{R}}(k,\omega,t)=\int_{\mathbb{R}}\Bigl(\tfrac{x-i}{\sqrt{1+x^2}}\Bigr)^{k}(1+x^2)^{-\omega}e^{-2\pi i t x}\,dx,\qquad j_{\mathbb{C}}(a,b,\omega,\zeta)=\int_{\mathbb{C}}z^{a}\bar z^{\,b}(1+\|z\|^2)^{-\omega}e^{-4\pi i\,\mathrm{Re}(\zeta z)}\,dz.$$
--
--   **Conclusion.** For each such family there exist $n\in\mathbb{N}$, functions $C_j:\mathbb{C}\to\mathbb{C}$ for $j<n$, integers $\mathrm{kdat}_j(i)$ at the real places, reals $\tau_{r,j}(i)$ at the real places, triples $\mathrm{abm}_j(v)=(a_{jv},b_{jv},m_{jv})\in\mathbb{N}^3$ at the complex places, reals $\tau_{c,j}(v)$ at the complex places, an idele unit $a$, an adele $u$, integers $\mathrm{thr}(v)$, and functions $\Phi_j(v,\cdot,\cdot):K_v\times\mathbb{C}\to\mathbb{C}$, such that: $n\le n_0$; $a=1$; $u=0$; $\tau_{r,j}(i)=\tau_\mu(i)-\tau_\nu(i)$ for all $j$ and all real places $i$; $\tau_{c,j}(v)=2(\tau_\mu(v)-\tau_\nu(v))$ for all $j$ and all complex places $v$; $|\mathrm{kdat}_j(i)|\le k_0$; $m_{jv}\le k_0$; $\mathrm{thr}(v)\le t_0$ for every finite place $v$; $\|C_j(s)\|\le C_0$ whenever $\sigma_1\le\mathrm{Re}\,s\le\sigma_2$; each $C_j$ is entire; $a_{jv}+b_{jv}\le m_{jv}$; $\mathrm{thr}(v)=0$ for $v\notin S$; each $\Phi_j(v,x,\cdot)$ is entire; for $v\notin S$ one has $\Phi_j(v,x,s)=1$ whenever $|x|_v=1$; $\Phi_j(v,x,s)=0$ whenever $x\ne 0$ and $|x|_v>q^{\,\mathrm{thr}(v)}$; on the strip, $\|\Phi_j(v,x,s)\|\le(\text{$M$ if }v\in S\text{, else }1)\cdot\bigl(\mathrm{absNorm}(v)^{(-e)^+}\bigr)^{\kappa}$ whenever $|x|_v=q^{\,e}$ and $\sigma_1\le\mathrm{Re}\,s\le\sigma_2$; for every $R$ there are $M'\ge 0$ and $\kappa'\in\mathbb{N}$ giving the same shape of bound, with $M'$ and $\kappa'$ in place of $M$ and $\kappa$, for all $\|s\|\le R$; and each $\Phi_j(v,\cdot,\cdot)$ is locally constant in its $K_v$-variable away from $0$, uniformly in $s$: for $x_0\ne0$ there is $\delta\in\mathbb{Z}$ with $\Phi_j(v,x,s)=\Phi_j(v,x_0,s)$ whenever $|x-x_0|_v\le q^{\,\delta}$.
--
--   The last conjunct is the factorisation itself: for every $s$ with $\mathrm{Re}\,s>1$, every non-zero $\xi\in K$ (a field element, not to be confused with the fixed character $\xi_K$) and every idele unit $y$, the Whittaker coefficient of $E(s,\cdot)$ along the torus element $\mathrm{diag}(y,1)$ — namely $\int \,E\bigl(s,u(x)\,\mathrm{diag}(y,1)\bigr)\,\psi(-\xi x)\,d\nu(x)$, where $\nu$ is, through `productionPins K`, the additive adelic Haar measure conditioned to the adelic box — equals
--   $$\nu(y)\,\|y\|^{1/2-s}\sum_{j<n}C_j(s)\cdot\Bigl(\tfrac{2^{r_2}}{\sqrt{|d_K|}}\cdot\bigl(\|a\|^{-1}\,\psi(\xi y u)\bigr)\Bigr)\cdot P_{\mathbb{R},j}\cdot P_{\mathbb{C},j}\cdot\Bigl(\textstyle\prod'_{v\notin S}\bigl(1-(\mu\nu^{-1})_v(\varpi_v)\,\mathrm{absNorm}(v)^{-(2s+1)}\bigr)\cdot\prod^{f}_{v}\Phi_j\bigl(v,(\xi y a^{-1})_v,s\bigr)\Bigr),$$
--   where $r_2$ is the number of complex places, $d_K$ the discriminant, $\|y\|^{1/2-s}$ is `cpowChar` of $\alpha_m$ at $1/2-s$, $\|a\|$ is the module of $a$, $(\mu\nu^{-1})_v$ is the local character of $\mu\nu^{-1}$ at $v$ evaluated at $\varpi_v$, the product over $v\notin S$ is an infinite product and the product of the $\Phi_j$ is a finitely-supported product over all finite places, with $(\xi y a^{-1})_v$ the $v$-component of the finite part of $\xi y a^{-1}$. The archimedean factors are
--   $$P_{\mathbb{R},j}=\prod_{i\ \mathrm{real}}j_{\mathbb{R}}\Bigl(\mathrm{kdat}_j(i),\ s+\tfrac12+\tfrac{i\,\tau_{r,j}(i)}{2},\ -\theta_r(i)\,x_i\Bigr),\qquad P_{\mathbb{C},j}=\prod_{v\ \mathrm{complex}}j_{\mathbb{C}}\Bigl(a_{jv},b_{jv},\ 2s+1+\tfrac{m_{jv}}{2}+\tfrac{i\,\tau_{c,j}(v)}{2},\ -\theta_c(v)\,z_v\Bigr),$$
--   where $x_i$ and $z_v$ are the real and complex coordinates of the infinite part of $\xi y a^{-1}$ under the identification of the infinite adeles with the mixed space. Since $a=1$ and $u=0$, the factors $\|a\|^{-1}$ and $\psi(\xi y u)$ are both $1$ and the arguments $\xi y a^{-1}$ reduce to $\xi y$.
--
--   This is the uniform form of the explicit factorisation of the Whittaker coefficients, along the diagonal torus, of Bruhat-form Eisenstein series on $\mathrm{GL}_2$ over a number field: the coefficient splits as a central twist, bounded entire scalars, archimedean Bessel-type integrals at the real and complex places, and a finite-place Euler product with locally constant local factors, all constants being chosen before the inducing character pair and the section family. It is cited by [`AutomorphicForm.exists_forall_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_norm_le_mul_pow_archParam_weight_dilation_of_flat`](thm.html#AutomorphicForm.exists_forall_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_norm_le_mul_pow_archParam_weight_dilation_of_flat), which converts the factorisation into an Euler product times an entire remainder with explicit growth in the archimedean parameters and the weight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat.lean

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat
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
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 K)) → AddChar (v.adicCompletion K) ℂ)
    (nψ : HeightOneSpectrum (𝓞 K) → ℤ)
    (_hnψfin : (Function.support nψ).Finite)
    (_hψv : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (_hψv' : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (_hψfin : ∀ x : FiniteAdeleRing (𝓞 K) K,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) x)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ψv v (x v))
    (θr : {w : InfinitePlace K // w.IsReal} → ℝ) (_hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace K // w.IsComplex} → ℂ) (_hθc : ∀ w, θc w ≠ 0)
    (_hψarch : ∀ p : mixedEmbedding.mixedSpace K,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm p))
      = (∏ i : {w : InfinitePlace K // w.IsReal},
      Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
      * ∏ w : {w : InfinitePlace K // w.IsComplex},
      Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (σ₁ σ₂ : ℝ)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (n₀ k₀ κ : ℕ) (t₀ : ℤ) (C₀ M : ℝ), SK ⊆ S ∧ 0 ≤ C₀ ∧ 0 ≤ M ∧
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
    let jR : ℤ → ℂ → ℝ → ℂ := fun k w t => ∫ x : ℝ,
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    let jC : ℕ → ℕ → ℂ → ℂ → ℂ := fun a b w ζ => ∫ z : ℂ,
      z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ (n : ℕ) (C : Fin n → ℂ → ℂ)
      (kdat : Fin n → {w : InfinitePlace K // w.IsReal} → ℤ)
      (τr : Fin n → {w : InfinitePlace K // w.IsReal} → ℝ)
      (abm : Fin n → {w : InfinitePlace K // w.IsComplex} → ℕ × ℕ × ℕ)
      (τc : Fin n → {w : InfinitePlace K // w.IsComplex} → ℝ)
      (a : (AdeleRing (𝓞 K) K)ˣ) (u : AdeleRing (𝓞 K) K)
      (thr : HeightOneSpectrum (𝓞 K) → ℤ)
      (Φ : Fin n → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ → ℂ),
      n ≤ n₀ ∧ a = 1 ∧ u = 0 ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace K // w.IsReal}), τr j i = τμ i.1 - τν i.1) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace K // w.IsComplex}), τc j w = 2 * (τμ w.1 - τν w.1)) ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace K // w.IsReal}), |kdat j i| ≤ (k₀ : ℤ)) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace K // w.IsComplex}), (abm j w).2.2 ≤ k₀) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), thr v ≤ t₀) ∧
      (∀ (j : Fin n) (s : ℂ), σ₁ ≤ s.re → s.re ≤ σ₂ → ‖C j s‖ ≤ C₀) ∧
      (∀ j, Differentiable ℂ (C j)) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace K // w.IsComplex}),
        (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ v ∉ S, thr v = 0) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K)) (w : v.adicCompletion K), Differentiable ℂ (Φ j v w)) ∧
      (∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion K) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K)) (w : v.adicCompletion K) (s : ℂ), w ≠ 0 →
        WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K))
        (w : v.adicCompletion K) (e : ℤ) (s : ℂ), σ₁ ≤ s.re → s.re ≤ σ₂ → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ) ∧
      (∀ R : ℝ, ∃ (M' : ℝ) (κ' : ℕ), 0 ≤ M' ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K))
        (w : v.adicCompletion K) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M' else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ') ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.adicCompletion K), w₀ ≠ 0 → ∃ δ : ℤ,
        ∀ (w : v.adicCompletion K) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) ∧
      ∀ (s : ℂ), 1 < s.re → ∀ (ξ : K), ξ ≠ 0 → ∀ y : (AdeleRing (𝓞 K) K)ˣ,
        whittakerCoefficient K (productionPins K) ψ (E s) ξ (diagOne y)
          = ((ν y : ℂˣ) : ℂ) * ((cpowChar αm hαm (1 / 2 - s) y : ℂˣ) : ℂ)
            * ∑ j : Fin n, C j s
              * ((((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
                  * ((((distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ≥0) : ℝ) : ℂ)⁻¹
                  * ψ (algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K) * u)))
              * (∏ i : {w : InfinitePlace K // w.IsReal},
                  jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
                    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace K
                      (algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K)
                        * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1).1 i)))
              * (∏ w : {w : InfinitePlace K // w.IsComplex},
                  jC (abm j w).1 (abm j w).2.1
                    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
                    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace K
                      (algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K)
                        * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1).2 w)))
              * ((∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
                * ∏ᶠ v : HeightOneSpectrum (𝓞 K),
                    Φ j v ((algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K)
                        * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) s) := by sorry
