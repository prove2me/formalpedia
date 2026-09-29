-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/61ff076d-283f-5ec7-baab-88a0efff6f14
-- title:
--   Level structure for a non-split twisted centralizer, [L:K]=2
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an extension of $K$ of degree $2$ (hypothesis `h2`: $\operatorname{finrank}_K L = 2$), and $\sigma : L \simeq_K L$ is a $K$-automorphism such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$ (`hgen`). For a commutative topological $K$-algebra $A$, write $X \mapsto X^{\sigma}$ for the entrywise action of the ring endomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K A$ (`sigmaTensor`, and `sigmaGL` on $\mathrm{GL}_2$), and for $\delta \in \mathrm{GL}_2(L \otimes_K A)$ let $T_{\delta} = \{t : t\,\delta\,(t^{\sigma})^{-1} = \delta\}$ be the $\sigma$-twisted centralizer (`twistedCentralizer`, i.e. `sigmaCentralizer` of `sigmaGL` at $\delta$); `normString` at $\delta$ is the product $\prod_{i<[L:K]} (\delta^{\sigma^{i}})$, here $\delta\,\delta^{\sigma}$, and `toTensorGL` is the map $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$.
--
--   The data are: $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c \in (L \otimes_K \mathbb{A}_K)^{\times}$ and an idele $u \in \mathbb{A}_K^{\times}$, and $\delta := (\delta_0 \otimes 1)\cdot cI \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, the product of the image of $\delta_0$ under $\ell \mapsto \ell \otimes 1$ with the scalar matrix of $c$. Two hypotheses constrain this class: `hN` states that $\delta\,\delta^{\sigma}$ is the scalar matrix of the image of $u$ in $(L \otimes_K \mathbb{A}_K)^{\times}$ (central norm); `hns` states that for all $x \in \mathrm{GL}_2(L)$ and $z \in L^{\times}$ one has $x^{-1}\delta_0\,\sigma(x) \neq zI$, so $\delta_0$ is not $\sigma$-conjugate over $L$ to a central element. Write $\delta_{\infty} =$ `tensorArch` $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and $\delta_v =$ `tensorPlace` $v\,\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ for a finite place $v$ (height-one prime of $\mathcal{O}_K$), the base changes of $\delta$ along $\mathbb{A}_K \to \mathbb{A}_{K,\infty}$ and $\mathbb{A}_K \to K_v$ tensored with the identity of $L$.
--
--   Local measures and their normalisations. $\tau_a'$ is a Haar measure (`hτa'`) on $T_{\delta_{\infty}}$, and for each finite place $v$, $\tau_f'(v)$ is a Haar measure (`hτf'`) on $T_{\delta_v}$; $s \in [0,\infty]$. The hypothesis `harch` (stated with the $\mathbb{R}$-algebra structure on $\mathbb{A}_{K,\infty}$ transported from the mixed space, the induced $\mathbb{R}$-algebra structure on $L \otimes_K \mathbb{A}_{K,\infty}$ via $a \mapsto 1\otimes a$, and the Borel $\sigma$-algebra on $M_2(L \otimes_K \mathbb{A}_{K,\infty})$) asserts the existence of $n_2 \in \mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K \mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly the $\sigma$-twisted commutant $\{X : X\delta_{\infty} = \delta_{\infty}X^{\sigma}\}$, together with the identity: the image of $\tau_a'$ under $t \mapsto$ (the underlying matrix of $t$) equals $s$ times the measure obtained from Lebesgue measure on $\mathbb{R}^{n_2}$ pushed forward by $(c_i) \mapsto \sum_i c_i e_2(i)$, scaled by $\sqrt{|\det(\mathrm{tr}_{\mathbb{R}}(\operatorname{tr}(e_2(i)e_2(j))))|}$ and given the density $X \mapsto |N_{\mathbb{R}}(\det X)|^{-1}$.
--
--   Local mass factors. $t : \{\text{finite places}\} \to [0,\infty]$, $S_0$ a finite set of finite places, with $t_v = 1$ for $v \notin S_0$ (`ht`). The hypothesis `hfin` requires, for every finite place $v$, one of two alternatives. First kind: there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ which is a norm conjugator (`IsNormConjugator`) from the $v$-component of the adelic scalar matrix $uI$ (obtained by `glFin` followed by `finComponent` at $v$, applied to `centralScalar` $u$) to $\delta_v$, that is, the image of that scalar matrix under `toTensorGL` equals $y^{-1}\,\delta_v\delta_v^{\sigma}\,y$, and the image of $\tau_f'(v)$ under $t \mapsto y^{-1}ty$ equals $t_v$ times the image under `toTensorGL` of `localHaar` $K\,v$, the Haar measure on $\mathrm{GL}_2(K_v)$ of total mass $1$ on the set of matrices with integral entries and integral inverse. Second kind: no scalar matrix $zI$, $z \in (L \otimes_K K_v)^{\times}$, is $\sigma$-conjugate to $\delta_v$ (`IsSigmaConjugate`: $zI = x^{-1}\delta_v x^{\sigma}$ for some $x$), and, writing $E_v$ for the set of $t \in T_{\delta_v}$ whose determinant is the image of some $s \in K_v^{\times}$ with $\mathrm{v}(s) = 1$, one has $\tau_f'(v)(E_v)\cdot \mathrm{N}(v) = t_v + \tau_f'(v)(E_v)$, where $\mathrm{N}(v) =$ `Ideal.absNorm` of $v$.
--
--   Global measure and product formula. $\tau'$ is a Haar measure (`hτ'`) on $T_{\delta}$, and $c_{\tau'} > 0$ is a real constant for which `hτ'prod` holds: for every finite set $S \supseteq S_0$ of finite places and all functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_a$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and $W_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$, all complex valued, such that $W_a$ is a.e. strongly measurable for $\tau_a'$ on $T_{\delta_\infty}$, each $W_S(v)$ ($v \in S$) is a.e. strongly measurable for $\tau_f'(v)$ on $T_{\delta_v}$, $W(t) = W_a(\text{tensorArch } t)\prod_{v\in S} W_S(v)(\text{tensorPlace } v\, t)$ for every $t \in T_{\delta}$ whose local components at all $v \notin S$ lie in `semiLocalIntegralSet` $K\,L\,v$ (the $g$ with all entries of $g$ and of $g^{-1}$ in `semiLocalIntegers` $K\,L\,v$, the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v}$ in $L \otimes_K K_v$), and $W(t) = 0$ whenever some component at a place outside $S$ fails to lie in that set, one has $\int W \, d\tau' = c_{\tau'}\,(\int W_a\, d\tau_a')\prod_{v\in S}\int W_S(v)\, d\tau_f'(v)$.
--
--   Finally, a nonzero column vector $\mathbf{v} : \mathrm{Fin}\,2 \to L$ (`hv`: $\mathbf{v} \neq 0$) is given, $\mathbb{A}_L$ carries a measurable space structure which is the Borel structure of its topology, and $\mu_1$ is an additive Haar measure on $\mathbb{A}_L$ with $\mu_1(\text{adelicBox } L) = 1$, the box being the product of the fundamental domain of the Minkowski lattice at the infinite places with the integral finite adeles.
--
--   Conclusion: there exist a finite set $S_1$ of finite places of $K$, sets $W_v \subseteq \mathrm{GL}_2(L \otimes_K K_v)$ for every finite place $v$, a set $U \subseteq (\mathbb{A}_{L,f})^2$ of pairs of finite adeles of $L$, and a function $\mathrm{Corr} : \{\text{finite places}\} \to \mathbb{R} \to [0,\infty]$, such that:
--
--   (i) $U$ is open; (ii) $U$ is compact; (iii) $U$ is nonempty; (iv) $S_0 \subseteq S_1$;
--
--   (v) each $W_v$ is measurable for the Borel $\sigma$-algebra `glBorelOf` on $\mathrm{GL}_2(L \otimes_K K_v)$;
--
--   (vi) for every $v \notin S_1$ and every $x \in T_{\delta_v}$: $x \in W_v$ if and only if all entries of the matrix of $x$ lie in `semiLocalIntegers` $K\,L\,v$;
--
--   (vii) for every finite set $S \supseteq S_1$ and every $t \in T_{\delta}$ whose local component at each $v \notin S$ lies in `semiLocalIntegralSet` $K\,L\,v$, the indicator of $U$ with value $1 \in \mathbb{C}$, evaluated at the point whose $i$-th coordinate is the finite-adelic component of the $i$-th coordinate of the product of the matrix over $\mathbb{A}_L$ obtained from $t$ by applying entrywise the composite of $\mathrm{Algebra.TensorProduct.comm}$, $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L$, with `genuineRingEquiv`, $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$, by the column vector $(\,\text{image of } \mathbf{v}(i) \text{ in } \mathbb{A}_L)_i$, equals $\prod_{v \in S}$ (indicator of $W_v$ with value $1$, evaluated at `tensorPlace` $v\,t$);
--
--   (viii) for every $v \notin S_1$ there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ which is a norm conjugator from the $v$-component of the adelic scalar matrix $uI$ to $\delta_v$ in the sense above, and the image of $\tau_f'(v)$ under $t \mapsto y^{-1}ty$ equals exactly the image under `toTensorGL` of `localHaar` $K\,v$ (mass factor $1$);
--
--   (ix) for every $v \in S_1$ and every real $s' \geq 1$,
--   $$\int^{-}_{\{t \in T_{\delta_v}\,:\, t \in W_v\}} \big\|N_{L\otimes_K K_v / K_v}(\det t)\big\|^{s'}\, d\tau_f'(v) = \mathrm{Corr}_v(s')\cdot \big(1 - \mathrm{N}(v)^{-2s'}\big)^{-1}\big(1 - \mathrm{N}(v)^{1-2s'}\big)^{-1},$$
--   the integrand being `ENNReal.ofReal` of that real power;
--
--   (x) for every $v \in S_1$: $\mathrm{Corr}_v(s') \neq \infty$ for all real $s' \geq 1$, and $\mathrm{Corr}_v(s') \to \mathrm{Corr}_v(1)$ as $s' \to 1^{+}$;
--
--   (xi) there is $n \in \mathbb{N}$ with $n > 0$ such that for every $x : \mathrm{Fin}\,2 \to \mathbb{A}_{L,f}$ with all $x(i)$ in `AdelicLevel.integralFiniteAdeles`, the vector $(n\,x(i))_i$ lies in $U$.
--
--   This is the level-structure step in the analysis of the $\sigma$-twisted orbital integrals attached to a non-split twisted class with central norm over a quadratic extension $L/K$: it produces a finite bad set $S_1$, local level sets $W_v$ equal to the integral lattice outside $S_1$, a compact open level $U$ in $(\mathbb{A}_{L,f})^2$ containing a dilate of the integral vectors, and local correction factors isolating the local zeta factors $(1-\mathrm{N}(v)^{-2s'})^{-1}(1-\mathrm{N}(v)^{1-2s'})^{-1}$. It is used by the Euler-product residue computation for Schwartz test functions on the twisted centralizer and by the finiteness statement for the corresponding weighted integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.lean

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

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
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
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1) :
    ∃ (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
      (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
      (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
      (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞),
      IsOpen U ∧ IsCompact U ∧ U.Nonempty ∧ S₀ ⊆ S₁ ∧
      (∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v)) ∧
      (∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
        ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
          ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
            AutomorphicForm.semiLocalIntegers K L v)) ∧
      (∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
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
              (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∧
      (∀ v ∉ S₁,
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
            Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))) ∧
      (∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
        ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
            ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
          Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹)) ∧
      (∀ v ∈ S₁, (∀ s' : ℝ, 1 ≤ s' → Corr v s' ≠ ⊤) ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1))) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ x : Fin 2 → FiniteAdeleRing (𝓞 L) L,
        (∀ i, x i ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) →
          (fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * x i) ∈ U) := by sorry
