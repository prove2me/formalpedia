-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
-- name    : AutomorphicForm.lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/15907b40-929a-5b70-b128-68a67a0af21a
-- title:
--   Euler factorisation of a twisted-centralizer zeta integral
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an extension of $K$ of degree $2$ (hypothesis `h2`), and $\sigma : L \simeq_K L$ is an automorphism such that every element of $L \simeq_K L$ lies in the subgroup of integer powers of $\sigma$ (hypothesis `hgen`). Fixed data are $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c$ of $L \otimes_K \mathbb{A}_K$ and a unit $u$ of $\mathbb{A}_K$, where $\mathbb{A}_K$ denotes `AdeleRing (𝓞 K) K`; write $\delta$ for the element $\mathrm{GL}_2(\iota)(\delta_0) \cdot \mathrm{scalar}(c)$ of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, with $\iota$ the inclusion `Algebra.TensorProduct.includeLeftRingHom` of $L$ into $L \otimes_K \mathbb{A}_K$. Its archimedean and $v$-adic images are $\delta_\infty =$ `tensorArch K L` $\delta \in \mathrm{GL}_2(L \otimes_K K_\infty)$ and $\delta_v =$ `tensorPlace K L v` $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$, obtained by base change of the archimedean and $v$-adic projections of $\mathbb{A}_K$; $\sigma$ acts on each of these matrix groups entrywise through `sigmaTensor`, i.e. through $\sigma \otimes \mathrm{id}$, and `sigmaGL` denotes the induced map on $\mathrm{GL}_2$. For a commutative $K$-algebra $A$ and $\delta' \in \mathrm{GL}_2(L \otimes_K A)$, the twisted centralizer `twistedCentralizer K L A σ δ'` is the subgroup $\{t : t\,\delta'\,\sigma(t)^{-1} = \delta'\}$, and `normString K L A σ δ'` is the product $\prod_{i<[L:K]} \sigma^{i}(\delta')$, here $\delta' \sigma(\delta')$.
--
--   Two conditions constrain the class of $\delta$: `hN` asserts that the norm string of $\delta$ equals the image of the central scalar matrix $\mathrm{scalar}(u) \in \mathrm{GL}_2(\mathbb{A}_K)$ under the base-change map `toTensorGL`; `hns` asserts that for no $x \in \mathrm{GL}_2(L)$ and $z \in L^{\times}$ is $x^{-1}\delta_0\,\sigma(x)$ a central scalar matrix.
--
--   Measure data at the places of $K$: $\tau_a'$ is a Haar measure on `twistedCentralizer K L (InfiniteAdeleRing K) σ` $\delta_\infty$ (`hτa'`), and for each finite place $v$ of $K$, $\tau_f'(v)$ is a Haar measure on `twistedCentralizer K L (v.adicCompletion K) σ` $\delta_v$ (`hτf'`). A constant $s \in [0,\infty]$ and the hypothesis `harch` normalise $\tau_a'$: with $\mathbb{R}$ acting on $K_\infty$ through the mixed-space description and on $L \otimes_K K_\infty$ through `includeRight`, and with the Borel structure on $M_2(L \otimes_K K_\infty)$, there exist $n_2 \in \mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K K_\infty)$ whose $\mathbb{R}$-span is exactly the set $\{X : X\delta_\infty = \delta_\infty \, \sigma(X)\}$, such that the pushforward of $\tau_a'$ along $t \mapsto$ (the matrix underlying $t$) equals $s$ times the measure obtained from Lebesgue measure on $\mathrm{Fin}\,n_2 \to \mathbb{R}$ by pushing forward along $cc \mapsto \sum_i cc_i \, e_2(i)$, scaling by $\sqrt{|\det G|}$ for the Gram matrix $G_{ij} = \mathrm{Tr}_{\mathbb{R}}^{L \otimes_K K_\infty}(\mathrm{tr}(e_2(i)e_2(j)))$, and taking the density $X \mapsto |\mathrm{N}_{\mathbb{R}}(\det X)|^{-1}$.
--
--   Local normalisations at the finite places are governed by a function $t$ from finite places to $[0,\infty]$, a finite set $S_0$ of finite places with $t(v) = 1$ for $v \notin S_0$ (`ht`), and the hypothesis `hfin`, which requires of every finite place $v$ one of two alternatives: either there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ which is a norm conjugator in the sense that `toTensorGL` applied to the $v$-component of the finite part of $\mathrm{scalar}(u)$ equals $y^{-1}\,\delta_v\,\sigma(\delta_v)\,y$, and the pushforward of $\tau_f'(v)$ under $t \mapsto y^{-1} t y$ equals $t(v)$ times the pushforward of the local Haar measure `localHaar K v` of $\mathrm{GL}_2(K_v)$ along `toTensorGL`; or else $\delta_v$ is $\sigma$-conjugate to no central scalar matrix (there is no $x$ with $\mathrm{scalar}(z) = x^{-1}\delta_v\,\sigma(x)$, for any unit $z$ of $L \otimes_K K_v$) and the measure $m_v$ under $\tau_f'(v)$ of the set of $t$ whose determinant is the image under `includeRight` of a unit $s$ of $K_v$ with $|s|_v = 1$ satisfies $m_v \cdot \mathrm{N}(v) = t(v) + m_v$, where $\mathrm{N}(v)$ is the absolute norm of the prime ideal of $v$.
--
--   Globally, $\tau'$ is a Haar measure on `twistedCentralizer K L (AdeleRing (𝓞 K) K) σ` $\delta$ (`hτ'`), $c_{\tau'} > 0$ is real (`hcτ'`), and `hτ'prod` is the factorisation clause: for every finite set $S \supseteq S_0$ of finite places and all complex-valued functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_a$ on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and $W_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$, if $W_a$ is a.e. strongly measurable for $\tau_a'$ and each $W_S(v)$ ($v \in S$) is a.e. strongly measurable for $\tau_f'(v)$, if $W(t) = W_a(t_\infty) \prod_{v \in S} W_S(v)(t_v)$ for every $t$ in the global twisted centralizer all of whose components $t_v$ with $v \notin S$ lie in `semiLocalIntegralSet K L v` (the set of $g$ with $g$ and $g^{-1}$ having all entries in the semi-local integers `semiLocalIntegers K L v`, the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v}$ in $L \otimes_K K_v$), and if $W(t) = 0$ whenever some $t_v$ with $v \notin S$ fails to lie in that set, then $\int W \, d\tau' = c_{\tau'} \left(\int W_a \, d\tau_a'\right) \prod_{v \in S} \int W_S(v) \, d\tau_f'(v)$.
--
--   The remaining data describe the level and the weight. A nonzero column vector $v \in L^2$ (`hv`); a Borel measurable space structure on $\mathbb{A}_L$ and an additive Haar measure $\mu_1$ on it with $\mu_1$ of the adelic box `adelicBox L` equal to $1$ (`hμ₁`); a set $U$ of column vectors over the finite adeles of $L$; a function $G$ from $M_2(L \otimes_K K_\infty)$ to $[0,\infty]$, Borel measurable (`hGm`); a finite set $S_1 \supseteq S_0$ (`hS₁`); and for each finite place $v$ a set $W(v) \subseteq \mathrm{GL}_2(L \otimes_K K_v)$, measurable for the Borel structure (`hWm`). Three compatibility hypotheses are imposed: `hW₀`, that for $v \notin S_1$ and $x$ in the local twisted centralizer, $x \in W(v)$ if and only if all entries of $x$ lie in `semiLocalIntegers K L v`; `hW₁`, the level dictionary, that for every finite $S \supseteq S_1$ and every $t$ in the global twisted centralizer whose components off $S$ are semi-locally integral, the indicator of $U$ (with value $1 \in \mathbb{C}$) evaluated at the finite-adelic parts of the coordinates of the vector obtained by applying to $(\,\mathrm{algebraMap}\,L\,\mathbb{A}_L\,(v_i)\,)_i$ the matrix over $\mathbb{A}_L$ image of $t$ under $\mathrm{GL}_2$ of the isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ given by `Algebra.TensorProduct.comm` followed by [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), equals $\prod_{v \in S}$ of the indicator of $W(v)$ at $t_v$; and `hunit`, that for $v \notin S_1$ there is a norm conjugator $y$ as above for which the pushforward of $\tau_f'(v)$ under $t \mapsto y^{-1} t y$ equals the pushforward of `localHaar K v` along `toTensorGL` exactly (constant $1$).
--
--   Finally, local correction factors: a function $\mathrm{Corr}$ assigning to each finite place a function on $\mathbb{R}$ with values in $[0,\infty]$, subject to `hCorr`, that for $v \in S_1$ and every real $s' \ge 1$,
--   $$\int_{\{t \in W(v)\}} \|\mathrm{N}_{K_v}(\det t)\|^{s'} \, d\tau_f'(v) = \mathrm{Corr}(v)(s') \cdot \left(1 - \mathrm{N}(v)^{-2s'}\right)^{-1}\left(1 - \mathrm{N}(v)^{1-2s'}\right)^{-1},$$
--   the integral being taken over the subset of the local twisted centralizer mapping into $W(v)$; and `hCorr₁`, that for $v \in S_1$ the value $\mathrm{Corr}(v)(1)$ is finite and $\mathrm{Corr}(v)(s') \to \mathrm{Corr}(v)(1)$ as $s' \to 1^{+}$.
--
--   The conclusion, stated with the same $\mathbb{R}$-algebra structures on $K_\infty$ and $L \otimes_K K_\infty$ as in `harch`, is the following. For every real $s' > 1$ satisfying the decay hypothesis — for all $n_2$ and all $\mathbb{R}$-linearly independent $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K K_\infty)$ whose $\mathbb{R}$-span equals $\{X : X \delta_\infty = \delta_\infty \sigma(X)\}$, there are reals $r, C$ with $n_2 + 2\,\dim_{\mathbb{R}}(L \otimes_K K_\infty)\,(s'-1) < r$ and $G\!\left(\sum_i cc_i\, e_2(i)\right) \le C(1+\|cc\|)^{-r}$ for all $cc : \mathrm{Fin}\,n_2 \to \mathbb{R}$ — one has the identity of $[0,\infty]$-valued integrals
--   $$\int G(t_\infty)\,\mathbf{1}_U(\text{finite part of } t \cdot v)\,\big(\|\det t\|_{\mathbb{A}_L}\big)^{s'} \, d\tau' = c_{\tau'} \cdot \left(\int G(t_\infty)\,|\mathrm{N}_{\mathbb{R}}(\det t_\infty)|^{s'}\, d\tau_a'\right) \cdot \left( \mathrm{Re}\big(\zeta_K(2s')\,\zeta_K(2s'-1)\big) \prod_{v \in S_1} \mathrm{Corr}(v)(s')\right),$$
--   where on the left $t$ ranges over the global twisted centralizer with measure $\tau'$, $t_\infty$ denotes the matrix underlying `tensorArch K L` $t$, the indicator is that of $U$ evaluated, as in `hW₁`, at the finite-adelic parts of the coordinates of the image of $(\,\mathrm{algebraMap}\,L\,\mathbb{A}_L\,(v_i)\,)_i$ under the matrix over $\mathbb{A}_L$ attached to $t$, and $\|\det t\|_{\mathbb{A}_L}$ is [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) of the determinant of that same image, i.e. the module of the idele $\det t$ measured by the distributive Haar character of $\mathbb{A}_L$; on the right the archimedean integral is over the archimedean twisted centralizer with measure $\tau_a'$, $\mathrm{N}_{\mathbb{R}}$ is the algebra norm of $L \otimes_K K_\infty$ over $\mathbb{R}$, and $\zeta_K$ is `NumberField.dedekindZeta K`, the real part of the product $\zeta_K(2s')\zeta_K(2s'-1)$ being inserted through `ENNReal.ofReal`.
--
--   This is the Euler-product assembly step for the global zeta integral of a twisted orbital integral attached to a regular $\sigma$-semisimple class $\delta$ over a quadratic extension $L/K$: the adelic integral over the twisted centralizer is expressed as the archimedean integral times a product of two Dedekind zeta factors of $K$ and finitely many local correction factors. It is used in the finiteness statement [`AutomorphicForm.exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two) and in the limit statement [`AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol`](thm.html#AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol), where the pole of $\zeta_K(2s'-1)$ at $s'=1$ produces the residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg.lean

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

theorem AutomorphicForm.lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
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
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G)
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
 :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    ∀ s' : ℝ, 1 < s' →
      (∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ →
        (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
            ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
              X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
        ∃ r C : ℝ, (n₂ : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s' - 1) < r ∧
          ∀ cc : Fin n₂ → ℝ, G (∑ i, cc i • e₂ i) ≤ ENNReal.ofReal (C * (1 + ‖cc‖) ^ (-r))) →
      (∫⁻ t, G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s') ∂τ') =
        ENNReal.ofReal cτ' *
          (∫⁻ ta, G ta.1.val * ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ta.1.val)| ^ s') ∂τa') *
          (ENNReal.ofReal ((NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) *
            NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re) *
            ∏ v ∈ S₁, Corr v s') := by sorry
