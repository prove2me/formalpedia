-- Prove2me | Theorems.Thm_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
-- name    : AutomorphicForm.exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f8b15782-a823-55bc-997a-7687f2093ffa
-- title:
--   Summable dominants and Lipschitz bounds for twisted Maass–Selberg pairings
-- statement:
--   Setting. Fix number fields $K$ and $L$ with $L$ a $K$-algebra, a datum $D$ of Galois descent on the adeles of $L$ (a homomorphism from $L\simeq_{\mathrm{alg}[K]}L$ to the ring automorphisms of $\mathbb{A}_L$, compatible with the map $L\to\mathbb{A}_L$ and continuous in each automorphism), an automorphism $\sigma$ of $L$ over $K$, an ideal $N$ of $\mathcal{O}_L$, an archimedean type family `tysL` for $L$ (at each infinite place a finite list of finite-dimensional representations of the row-isometry group of the completion), a finite set $S$ of primes of $\mathcal{O}_K$, a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, a family $\varphi_S$ assigning to each prime $v$ of $\mathcal{O}_K$ a function on $\mathrm{GL}_2(L\otimes_K K_v)$, a real weight $w$, and a homomorphism $\xi'$ from the full unit group of $\mathbb{A}_L$ to $\mathbb{C}^\times$. Throughout, $\alpha_m$ denotes the homomorphism from $\mathbb{A}_L^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_L$ through $\mathbb{R}_{\ge 0}\to\mathbb{R}$, the adeles carry the Borel $\sigma$-algebra, and $\mathtt{hαm}$ asserts that all values of $\alpha_m$ are positive.
--
--   Eisenstein data. The further universally quantified data are: a countable index type $\iota_E$ and families $\mu_E,\nu_E$ of homomorphisms $\mathbb{A}_L^\times\to\mathbb{C}^\times$, subject to the hypotheses `_hμ`, `_hν` (each $\mu_E e$, $\nu_E e$ has all values of absolute value $1$), `_hμic`, `_hνic` (each is trivial on the principal ideles, i.e. on the image of $L^\times$), `_hμc`, `_hνc` (continuity of the associated $\mathbb{C}$-valued functions), `_hμν` (for all $e$ and all $z$, $\mu_E e(z)\,\nu_E e(z)\,\lVert z\rVert^{w}=\xi'(z)$, where $\lVert\cdot\rVert$ is the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) and `_hdist` (distinct indices give pairs differing at some norm-one idele, i.e. some $z$ in the kernel of the distributive Haar character with $\mu_E e(z)\ne\mu_E e'(z)$ or $\nu_E e(z)\ne\nu_E e'(z)$).
--
--   Sections. Further data are $n_E:\iota_E\to\mathbb{N}$ and, for each $e$, functions $\varphi_E\,e\,j:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ for $j<n_E e$, subject to the following hypotheses. `_hφE`: each $\varphi_E\,e\,j\,s$ is an induced section for the pair $\eta_1=\mu_E e\cdot\alpha_m^{\,s+1/2}$, $\eta_2=\nu_E e\cdot\alpha_m^{-(s+1/2)}$, that is, $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for every $b$ in the adelic Borel subgroup (lower-left entry zero) and every $g$. `_hφEK`: archimedean $K$-finiteness at every infinite place, the right translates under the archimedean row-isometry subgroup spanning a finite-dimensional space. `_hφEf`: smoothness under the finite-adelic subgroup (kernel of the archimedean projection), in the sense that the stabiliser of the right-translation function is open. `_hφEjc`: joint continuity in $(s,g)$. `_hφEhol`: entirety in $s$ for each $g$. `_hφEKu`: a uniform form of $K$-finiteness, a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at each infinite place containing all the functions $k\mapsto\varphi_E\,e\,j\,s\,(gk)$. `_hφEflat`: flatness, $\varphi_E\,e\,j\,s\,(k)=\varphi_E\,e\,j\,0\,(k)$ for $k$ in the adelic maximal compact subgroup (finite part integral, archimedean components row isometries). `_hφElev`: right invariance under the intersection of the principal level subgroup of $N$ with the finite-adelic subgroup. `_hφEty`: membership in the archimedean cut submodule determined by `tysL`. `_hφEon`: orthonormality at $s=0$, $\int_{\mathbf{K}}\varphi_E\,e\,i\,0(k)\,\overline{\varphi_E\,e\,j\,0(k)}\,dk=\delta_{ij}$ for the Haar measure `maximalCompactHaar` on the adelic maximal compact $\mathbf{K}$. `_hφEspan`: completeness on the unitary axis, every continuous, archimedean $K$-finite, level-$N$-invariant function of the prescribed archimedean types which is an induced section for the pair attached to $(\mu_E e,\nu_E e)$ at $s=it$ lies in the span of the $\varphi_E\,e\,j\,(it)$. `_hpairs`: exhaustiveness of the list of character pairs, namely for every pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'\lVert\cdot\rVert^{w}=\xi'$ and every nonzero continuous, archimedean $K$-finite, level-$N$-invariant induced section $\varphi_0$ of the prescribed types at $s=it$, there is an index $e$ with $\mu_E e=\mu'$ and $\nu_E e=\nu'$ on the norm-one ideles.
--
--   Continuations. Further data are sets $O_E\,e\,j\subseteq\mathbb{C}$ and functions $E_E\,e\,j$, $N_E\,e\,j$ of $(s,g)$, subject to the hypothesis `_hEE`: each $O_E\,e\,j$ is open, preconnected and contains both the imaginary axis $\{\Re s=0\}$ and the half-plane $\{\Re s>1/2\}$; for each $g$ both $s\mapsto E_E\,e\,j\,s\,g$ and $s\mapsto N_E\,e\,j\,s\,g$ are analytic on a neighbourhood of each point of $O_E\,e\,j$; both $(s,g)\mapsto E_E\,e\,j\,s\,g$ and $(s,g)\mapsto N_E\,e\,j\,s\,g$ are continuous on $O_E\,e\,j$ times the whole group; and for $\Re s>1/2$ and all $g$ one has $E_E\,e\,j\,s\,g=\varphi_E\,e\,j\,s\,g+\sum_{\xi\in L}\varphi_E\,e\,j\,s\,(\mathbf{w}\,u(\xi)\,g)$, with $\mathbf{w}$ the adelic Weyl element (image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$) and $u(\xi)$ the upper unipotent matrix of the idele of $\xi$, and $N_E\,e\,j\,s\,g=\int_{\mathbb{A}_L}\varphi_E\,e\,j\,s(\mathbf{w}^{-1}u(x)g)\,dx$ for the additive adelic Haar measure.
--
--   Test function. Finally, a continuous $\varphi_0$ on $\mathrm{GL}_2(\mathbb{A}_L)$ with compact support and a function $\varphi_{f,0}$ on $\mathrm{GL}_2$ of the finite adeles of $L$ are given, subject to the hypothesis that $(\varphi_0,\varphi_a,\varphi_{f,0},\varphi_S)$ is a semi-local factorisation above $S$: $\varphi_a$ is an archimedean test factor (compactly supported and of the form $\Phi$ applied to the matrix entries in the mixed space, with $\Phi$ smooth), $\varphi_{f,0}$ is locally constant with compact support, each $\varphi_S v$ for $v\in S$ is locally constant with compact support, $\varphi_{f,0}(h)=\prod_{v\in S}\varphi_S v(h_v)$ whenever all semi-local components of $h$ outside $S$ are integral, $\varphi_{f,0}(h)=0$ as soon as some semi-local component outside $S$ is not integral, and $\varphi_0(g)=\varphi_a(g_\infty)\,\varphi_{f,0}(g_f)$.
--
--   Pairings. The statement introduces, with all integrals over $\mathbf{K}$ against `maximalCompactHaar` and with $\sigma$ acting on $\mathrm{GL}_2(\mathbb{A}_L)$ entrywise through $D$ applied to $\sigma^{-1}$, the quantities
--   $$a_{e,ij}(t)=\int_{\mathbf{K}}\Big(\textstyle\int_{\mathrm{GL}_2(\mathbb{A}_L)}\varphi_E\,e\,j\,(it)(kx)\,\lVert\det(kx)\rVert^{w/2}\varphi_0(x)\,dx\Big)\overline{\varphi_E\,e\,i\,(it)(k)}\,dk,$$
--   the inner integral being the right convolution `rightConv` against the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$; $P_{e,ij}=\int_{\mathbf{K}}\varphi_E\,e\,i\,0(k)\,\overline{\varphi_E\,e\,j\,0(k^{\sigma})}\,dk$; and, writing $c=\big(\mathrm{vol}(\text{adelic box})\big)^{-1}$ for the inverse of the real volume of `adelicBox` under the additive adelic Haar measure,
--   $$Q_{e,ij}(t)=\int_{\mathbf{K}} c\,N_E\,e\,i\,(it)(k)\,\overline{c\,\partial_s\big(N_E\,e\,j\,s\,(k^{\sigma})\big)\big|_{s=it}}\,dk,$$
--   $$U_{e,ij}(t)=\int_{\mathbf{K}}\varphi_E\,e\,i\,(it)(k)\,\overline{c\,N_E\,e\,j\,(it)(k^{\sigma})}\,dk,\qquad V_{e,ij}(t)=\int_{\mathbf{K}} c\,N_E\,e\,i\,(it)(k)\,\overline{\varphi_E\,e\,j\,(it)(k^{\sigma})}\,dk.$$
--
--   Conclusion. Under all of the above the following hold: the functions $t\mapsto a_{e,ij}(t)$, $t\mapsto Q_{e,ij}(t)$, $t\mapsto U_{e,ij}(t)$ and $t\mapsto V_{e,ij}(t)$ are continuous for all $e,i,j$; each $a_{e,ij}$ is integrable on $\mathbb{R}$; each of $t\mapsto a_{e,ij}(t)Q_{e,ij}(t)$, $t\mapsto a_{e,ij}(t)U_{e,ij}(t)$ and $t\mapsto a_{e,ij}(t)V_{e,ij}(t)$ is integrable on $\mathbb{R}$; and there exists $L^{\flat}:\iota_E\to\mathbb{R}$ which is summable and such that, for every $e$,
--   $$\sum_{i,j<n_E e}\int_{\mathbb{R}}\Big(\lVert a_{e,ij}(t)\rVert\big(1+\lVert P_{e,ij}\rVert\big)+\lVert a_{e,ij}(t)Q_{e,ij}(t)\rVert+\lVert a_{e,ij}(t)U_{e,ij}(t)\rVert+\lVert a_{e,ij}(t)V_{e,ij}(t)\rVert\Big)\,dt\le L^{\flat}(e),$$
--   for every $e$ and every $t$,
--   $$\sum_{i,j<n_E e}\lVert a_{e,ij}(t)\rVert\big(\lVert U_{e,ij}(t)\rVert+\lVert V_{e,ij}(t)\rVert\big)\le L^{\flat}(e),$$
--   and for every $e$ and all real $t,t'$ both Lipschitz estimates
--   $$\sum_{i,j<n_E e}\big\lVert a_{e,ij}(t)\big(U_{e,ij}(t)+V_{e,ij}(t)\big)-a_{e,ij}(t')\big(U_{e,ij}(t')+V_{e,ij}(t')\big)\big\rVert\le L^{\flat}(e)\,|t-t'|,$$
--   $$\sum_{i,j<n_E e}\big\lVert a_{e,ij}(t)\big(U_{e,ij}(t)-V_{e,ij}(t)\big)-a_{e,ij}(t')\big(U_{e,ij}(t')-V_{e,ij}(t')\big)\big\rVert\le L^{\flat}(e)\,|t-t'|.$$
--
--   This is the analytic package for the continuous spectrum in the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L/K$: it provides a single summable majorant, uniform in the spectral parameter, for the coefficients $a_{e,ij}$ of the Eisenstein contribution paired against the $\sigma$-twisted Maass–Selberg quantities $P$, $Q$, $U$, $V$, together with Lipschitz control in $t$ of the combinations $a(U\pm V)$. It is used in the assembly of the continuous term of the twisted formula, in [`AutomorphicForm.exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
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
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (w : ℝ) (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
      (μE νE : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μE e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (νE e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μE e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (νE e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ),
        ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μE e z ≠ μE e' z ∨ νE e z ≠ νE e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm s) (etaSnd (νE e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite L (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth L (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 L) L), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace L), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φE e j s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
        φE e j s (k : AdelicGL2 (𝓞 L) L) = φE e j 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule L tysL)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νE e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μE' νE' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μE' → IsUnitaryChar (𝓞 L) L νE' →
        IsIdeleClassChar (𝓞 L) L μE' → IsIdeleClassChar (𝓞 L) L νE' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ((μE' z : ℂˣ) : ℂ) * ((νE' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μE' αm hαm ((t : ℂ) * Complex.I)) (etaSnd νE' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z = μE' z ∧ νE e z = νE' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        EE e j s g = φE e j s g + ∑' ξ : L, φE e j s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        NE e j s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φE e j s) g))
      (φ₀ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ₀ : Continuous φ₀) (_hφ₀c : HasCompactSupport φ₀)
      (φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L S φ₀ φa φf₀ φS →
    let a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ₀ (k : AdelicGL2 (𝓞 L) L) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)
    let P : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℂ := fun e i j =>
      ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    let Q : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => NE e j s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    let U : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    let V : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (φE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    (∀ e i j, Continuous (a e i j)) ∧ (∀ e i j, Continuous (Q e i j)) ∧
    (∀ e i j, Continuous (U e i j)) ∧ (∀ e i j, Continuous (V e i j)) ∧
    (∀ e i j, Integrable (a e i j)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * Q e i j t)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * U e i j t)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * V e i j t)) ∧
    ∃ Lb : ιE → ℝ, Summable Lb ∧
      (∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ Lb e) ∧
      (∀ (e : ιE) (t : ℝ), ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t‖ * (‖U e i j t‖ + ‖V e i j t‖) ≤ Lb e) ∧
      (∀ (e : ιE) (t t' : ℝ),
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t + V e i j t) - a e i j t' * (U e i j t' + V e i j t')‖) ≤ Lb e * |t - t'| ∧
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t - V e i j t) - a e i j t' * (U e i j t' - V e i j t')‖) ≤ Lb e * |t - t'|) := by sorry
