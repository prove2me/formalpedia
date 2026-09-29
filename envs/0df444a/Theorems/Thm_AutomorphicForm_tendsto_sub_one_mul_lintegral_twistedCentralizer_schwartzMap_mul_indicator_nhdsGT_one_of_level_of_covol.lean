-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol
-- name    : AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/eb334f25-d50e-5a47-b3a1-4d9b795c692a
-- title:
--   Euler limit of the twisted-centralizer zeta integral at a level
-- statement:
--   Throughout, $\mathbb{A}_K$ denotes `AdeleRing (𝓞 K) K`, $\mathbb{A}_{K,\infty}$ the infinite adeles of $K$, $K_v$ the completion at a finite place $v$ of $K$, and $\mathbb{A}_L$ the adeles of $L$.
--
--   **Data.** Number fields $K\subseteq L$ with $\operatorname{finrank}_K L=2$ (hypothesis `h2`), an automorphism $\sigma\in\operatorname{Aut}_K(L)$ such that every $\tau\in\operatorname{Aut}_K(L)$ lies in the subgroup of integer powers of $\sigma$ (`hgen`), a matrix $\delta_0\in GL_2(L)$, a unit $c\in(L\otimes_K\mathbb{A}_K)^\times$ and a unit $u\in\mathbb{A}_K^\times$. Write $\delta\in GL_2(L\otimes_K\mathbb{A}_K)$ for the product of the image of $\delta_0$ under the entrywise map induced by $L\to L\otimes_K\mathbb{A}_K$ with the scalar matrix $cI$, write $\sigma_{GL}$ for the entrywise action of $\sigma\otimes\mathrm{id}$ on $GL_2$ of a tensor product, and for a ring $A$ over $K$ let the twisted centraliser of an element $\epsilon$ be $\{t: t\,\epsilon\,\sigma_{GL}(t)^{-1}=\epsilon\}$. Put $\delta_\infty$ and $\delta_v$ for the images of $\delta$ in $GL_2(L\otimes_K\mathbb{A}_{K,\infty})$ and $GL_2(L\otimes_K K_v)$, and $T'$, $T'_\infty$, $T'_v$ for the twisted centralisers of $\delta$, $\delta_\infty$, $\delta_v$.
--
--   **Conditions on the twisted data.** `hN` requires $\delta\cdot\sigma_{GL}(\delta)=uI$, the norm string of $\delta$ (the product of $\sigma_{GL}^i(\delta)$ for $i<\operatorname{finrank}_K L$) being the image of the central scalar $u$ under the map $GL_2(\mathbb{A}_K)\to GL_2(L\otimes_K\mathbb{A}_K)$ induced by $a\mapsto 1\otimes a$. `hns` requires that $x^{-1}\delta_0\,\sigma_{GL}(x)\neq zI$ for all $x\in GL_2(L)$ and $z\in L^\times$.
--
--   **Measures.** $\tau_\infty'$ is a Haar measure on $T'_\infty$ (`hτa'`) and, for each finite place $v$, $\tau_v'$ is a Haar measure on $T'_v$ (`hτf'`). An extended non-negative real $s$ is given; in the limit statement below the bound real variable of the same name shadows it in the Lean text, and this constant $s$ is the scaling factor occurring in `harch`. The hypothesis `harch` (an archimedean Gram normalisation, stated for the $\mathbb{R}$-algebra structures on $\mathbb{A}_{K,\infty}$ and on $L\otimes_K\mathbb{A}_{K,\infty}$ coming from the mixed-space description of $\mathbb{A}_{K,\infty}$, and the Borel structure on $2\times2$ matrices) asserts the existence of $n_2\in\mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2:\mathrm{Fin}\,n_2\to M_2(L\otimes_K\mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly $\{X: X\delta_\infty=\delta_\infty\,\sigma_{GL}(X)\}$ (entrywise $\sigma\otimes\mathrm{id}$ applied to $X$), such that the push-forward of $\tau_\infty'$ along the inclusion $T'_\infty\hookrightarrow M_2(L\otimes_K\mathbb{A}_{K,\infty})$ equals $s$ times the measure obtained from $\sqrt{|\det G|}$ times the push-forward of Lebesgue measure on $\mathbb{R}^{n_2}$ under $c\mapsto\sum_i c_i e_2(i)$, taken with density $X\mapsto |N_{\mathbb{R}}(\det X)|^{-1}$, where $G$ is the Gram matrix $G_{ij}=\operatorname{Tr}_{(L\otimes_K\mathbb{A}_{K,\infty})/\mathbb{R}}\bigl(\operatorname{tr}(e_2(i)e_2(j))\bigr)$.
--
--   **Local normalising factors.** A function $t:\{\text{finite places}\}\to[0,\infty]$ and a finite set $S_0$ of finite places are given with $t_v=1$ for $v\notin S_0$ (`ht`). The hypothesis `hfin` requires, for every finite place $v$, one of two alternatives. Either there is $y\in GL_2(L\otimes_K K_v)$ which is a norm conjugator in the sense that the image in $GL_2(L\otimes_K K_v)$ of the $v$-component of the central scalar matrix $u$ equals $y^{-1}\,(\text{norm string of }\delta_v)\,y$, and the push-forward of $\tau_v'$ under $t\mapsto y^{-1}ty$ equals $t_v$ times the push-forward of the local Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $GL_2(K_v)$ under the map $GL_2(K_v)\to GL_2(L\otimes_K K_v)$. Or else: no scalar matrix is $\sigma$-conjugate to $\delta_v$ (there is no $x$ and no $z\in(L\otimes_K K_v)^\times$ with $zI=x^{-1}\delta_v\,\sigma_{GL}(x)$), and, writing $A_v\subseteq T'_v$ for the set of $t$ whose determinant is the image of some $s'\in K_v^\times$ with $|s'|_v=1$, the identity $\tau_v'(A_v)\cdot N(v)=t_v+\tau_v'(A_v)$ holds, $N(v)$ being the absolute norm of the prime ideal $v$.
--
--   **Global measure and its factorisation.** $\tau'$ is a Haar measure on $T'$ (`hτ'`), $c_{\tau'}$ is a real number with $c_{\tau'}>0$ (`hcτ'`), and `hτ'prod` is the restricted-product rule: for every finite set $S$ of finite places containing $S_0$ and all functions $W$ on $GL_2(L\otimes_K\mathbb{A}_K)$, $W_\infty$ on $GL_2(L\otimes_K\mathbb{A}_{K,\infty})$ and $W_v$ on $GL_2(L\otimes_K K_v)$ with complex values, if $W_\infty$ is almost everywhere strongly measurable for $\tau_\infty'$ and each $W_v$ ($v\in S$) for $\tau_v'$, if $W(t)=W_\infty(t_\infty)\prod_{v\in S}W_v(t_v)$ for every $t\in T'$ whose image $t_v$ lies in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) for all $v\notin S$ (that is, both $t_v$ and its inverse have all entries in the image of $\mathcal{O}_L\otimes_{\mathcal{O}_K}\mathcal{O}_{K_v}\to L\otimes_K K_v$), and if $W(t)=0$ for every $t\in T'$ failing this integrality at some $v\notin S$, then $\int W\,d\tau'=c_{\tau'}\bigl(\int W_\infty\,d\tau_\infty'\bigr)\prod_{v\in S}\int W_v\,d\tau_v'$.
--
--   **The test vector, the adelic Haar measure and the level.** A non-zero vector $v\in L^2$ is given (`hv`); $\mathbb{A}_L$ carries a Borel measurable structure and an additive Haar measure $\mu_1$ normalised by $\mu_1(\mathrm{adelicBox}\,L)=1$ (`hμ₁`), the box being the set of adeles whose infinite part lies in the fundamental domain of the lattice of $\mathcal{O}_L$ in the mixed space and whose finite part is everywhere integral. Further data: a set $U\subseteq(\mathbb{A}_{L,f})^2$; a Schwartz function $g$ on $(\text{mixed space of }L)^2$ with values in $\mathbb{C}$, of compact support (`hg`) and with $\operatorname{Re}g\ge0$, $\operatorname{Im}g=0$ pointwise (`hg'`); a finite set $S_1\supseteq S_0$ (`hS₁`); and sets $W_v\subseteq GL_2(L\otimes_K K_v)$, Borel measurable (`hWm`). For $t\in T'$ let $E(t)\in GL_2(\mathbb{A}_L)$ denote the image of $t$ under the entrywise ring isomorphism $L\otimes_K\mathbb{A}_K\cong\mathbb{A}_K\otimes_K L\cong\mathbb{A}_L$ (the commutation isomorphism followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57)), and let $\mathrm{col}(t)=E(t)\cdot(\text{image of }v\text{ in }\mathbb{A}_L^2)$. The level hypotheses are: `hW₀`, that for $v\notin S_1$ and $x\in T'_v$ one has $x\in W_v$ if and only if all entries of $x$ lie in the image of $\mathcal{O}_L\otimes_{\mathcal{O}_K}\mathcal{O}_{K_v}$; `hW₁`, that for every finite $S\supseteq S_1$ and every $t\in T'$ integral outside $S$ in the above sense, the indicator of $U$ evaluated at the finite-adelic part of $\mathrm{col}(t)$ equals $\prod_{v\in S}\mathbf 1_{W_v}(t_v)$; and `hunit`, that for $v\notin S_1$ there is a norm conjugator $y$ as in the first alternative of `hfin` for which the push-forward of $\tau_v'$ under $t\mapsto y^{-1}ty$ equals the push-forward of [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) exactly (mass one).
--
--   **Local correction factors.** A family $\mathrm{Corr}_v:\mathbb{R}\to[0,\infty]$ is given with: `hCorr`, for $v\in S_1$ and every real $s'\ge1$,
--   $$\int_{\{t\in T'_v\,:\,t\in W_v\}}\bigl\|N_{(L\otimes_K K_v)/K_v}(\det t)\bigr\|^{s'}\,d\tau_v'=\mathrm{Corr}_v(s')\bigl(1-N(v)^{-2s'}\bigr)^{-1}\bigl(1-N(v)^{1-2s'}\bigr)^{-1},$$
--   and `hCorr₁`, for $v\in S_1$, $\mathrm{Corr}_v(1)\neq\infty$ and $\mathrm{Corr}_v(s')\to\mathrm{Corr}_v(1)$ as $s'\to1^+$.
--
--   **The covolume identity.** The hypothesis `hE8` requires, for the same $\mathbb{R}$-algebra and Borel conventions as in `harch`, and for every $n_2$ and every $\mathbb{R}$-linearly independent $e_2:\mathrm{Fin}\,n_2\to M_2(L\otimes_K\mathbb{A}_{K,\infty})$ whose span is $\{X:X\delta_\infty=\delta_\infty\,\sigma_{GL}(X)\}$, the equality
--   $$\sqrt{|\det G|}\cdot\Bigl(\int^-_{\mathbb{R}^{n_2}}\operatorname{Re}g\Bigl(i\mapsto \bigl(\textstyle\sum_k c_k e_2(k)\bigr)\cdot(v_j\otimes1)\Bigr)_i\,dc\Bigr)\cdot\prod_{v\in S_1}\mathrm{Corr}_v(1)$$
--   $$=\Bigl(\int^-_{(\mathbb{A}_L)^2}\operatorname{Re}\bigl(g(x_\infty)\,\mathbf 1_U(x_f)\bigr)\,d(\mathrm{pairHaar}\,\mu_1)\Bigr)\cdot 2^{2\operatorname{finrank}_{\mathbb{Q}}K}\cdot\prod_{v\in S_0}t_v\cdot\operatorname{disc}(K)^2,$$
--   where on the left the entries of the matrix-vector product are carried into the mixed space of $L$ by the ring map $L\otimes_K\mathbb{A}_{K,\infty}\to\mathbb{A}_{L,\infty}$ and the mixed-space identification, where `pairHaar` $\mu_1$ is the product measure $\mu_1\otimes\mu_1$ on $(\mathbb{A}_L)^2$, and where all integrals are lower Lebesgue integrals of the $[0,\infty]$-valued functions obtained by taking real parts.
--
--   **Conclusion.** As the real variable $s$ tends to $1$ from above,
--   $$(s-1)\int^-_{T'}\operatorname{Re}\Bigl(g\bigl(\text{infinite part of }\mathrm{col}(t)\bigr)\cdot\mathbf 1_U\bigl(\text{finite part of }\mathrm{col}(t)\bigr)\Bigr)\cdot\bigl|\det E(t)\bigr|_{\mathbb{A}_L}^{\,s}\,d\tau'(t)$$
--   converges in $[0,\infty]$ to
--   $$\tfrac12\Bigl(\int^-_{(\mathbb{A}_L)^2}\operatorname{Re}\bigl(g(x_\infty)\,\mathbf 1_U(x_f)\bigr)\,d(\mathrm{pairHaar}\,\mu_1)\Bigr)\cdot\Bigl(c_{\tau'}\cdot s\cdot 2^{2\operatorname{finrank}_{\mathbb{Q}}K}\cdot\prod_{v\in S_0}t_v\cdot\bigl(\operatorname{disc}(K)^2\cdot\operatorname{Re}\zeta_K(2)\cdot\operatorname{res}_{s=1}\zeta_K\bigr)\Bigr),$$
--   where $s$ in the second factor is the extended non-negative real of `harch`, $|\cdot|_{\mathbb{A}_L}$ is the idele norm of $L$ (the distributive Haar character of $\mathbb{A}_L$ read as a real number), $\zeta_K$ is the Dedekind zeta function of $K$ and $\operatorname{res}_{s=1}\zeta_K$ its residue at $1$; the convergence is stated for the filter of right neighbourhoods of $1$ in $\mathbb{R}$, and all the scalar factors, infinite integrals and powers are formed in $[0,\infty]$ by way of `ENNReal.ofReal`.
--
--   This is the residue computation for the global zeta integral of a Schwartz test function against the twisted centraliser of $\delta$ in $GL_2(L\otimes_K\mathbb{A}_K)$, with the level data $(U,g,S_1,W,\mathrm{Corr})$ fixed in advance: the Euler product is factorised by the restricted-product rule, the finite places outside $S_1$ contribute the two Dedekind zeta factors, and the archimedean Gram normalisation together with the covolume identity identifies the limit with a Tamagawa-type volume of $\mathbb{A}_L^2$. It is used by [`AutomorphicForm.exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two), which produces such level data and then appeals to this limit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open NumberField

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical in

theorem AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ)) (hg : HasCompactSupport g)
    (hg' : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hS₁ : S₀ ⊆ S₁)
    (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hWm : ∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v))
    (hW₀ : ∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L v))
    (hW₁ : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          AutomorphicForm.semiLocalIntegralSet K L v) →
        U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
          ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
            (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))
    (hunit : ∀ v ∉ S₁,
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
        Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))
    (hCorr₁ : ∀ v ∈ S₁, Corr v 1 ≠ ⊤ ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)))
    (hE8 :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
          ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
            X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
            Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
          ∫⁻ cc : Fin n₂ → ℝ, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L (((∑ k, cc k • e₂ k).mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re) *
        ∏ v ∈ S₁, Corr v 1 =
      (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
        2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) * ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        ∫⁻ t, ENNReal.ofReal
          (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1) *
            U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2)).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s) ∂τ')
        (𝓝[>] (1 : ℝ))
        (𝓝 (2⁻¹ * ((∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
          (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
            ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
              NumberField.dedekindZeta_residue K))))) := by sorry
