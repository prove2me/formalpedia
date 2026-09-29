-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two
-- name    : AutomorphicForm.exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/cb3aed7e-5861-524f-93da-732ea26eb703
-- title:
--   Residue of the twisted-centralizer zeta integral for standard test functions
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ of degree $\operatorname{finrank}_K L = 2$ (hypothesis `h2`), and let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$ (hypothesis `hgen`). Fix $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c$ of $L \otimes_K \mathbb{A}_K$ and a unit $u$ of $\mathbb{A}_K$, and write $\delta$ for the element $\mathrm{GL}_2$ of the inclusion $L \to L \otimes_K \mathbb{A}_K$ applied to $\delta_0$, multiplied by the scalar matrix with entry $c$. Throughout, $\sigma$ acts on $\mathrm{GL}_2(L \otimes_K A)$ entrywise through [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199), i.e. through $\sigma \otimes \mathrm{id}_A$, and [`AutomorphicForm.twistedCentralizer K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L220) denotes the subgroup $\{t \mid t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\mathrm{GL}_2(L \otimes_K A)$, all such groups and centralizers carrying their Borel $\sigma$-algebras.
--
--   Two hypotheses constrain $\delta$. The hypothesis `hN` requires that the norm string [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205), the product $\prod_{i < \operatorname{finrank}_K L} \sigma^i(\delta)$, which under `h2` is $\delta\,\sigma(\delta)$, equals the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) (base change along $\mathbb{A}_K \to L \otimes_K \mathbb{A}_K$) of the scalar matrix $\mathrm{diag}(u,u)$. The hypothesis `hns` requires that $x^{-1}\,\delta_0\,\sigma(x)$ is never a scalar matrix with entry in $L^\times$, for $x \in \mathrm{GL}_2(L)$ and the scalar ranging over $L^\times$.
--
--   The local data consist of: a Haar measure $\tau_\infty'$ on the $\sigma$-twisted centralizer of the archimedean base change [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46) of $\delta$ in $\mathrm{GL}_2(L \otimes_K K_\infty)$ (hypotheses `τa'`, `hτa'`); for each finite place $v$ of $K$, i.e. each $v$ in the height-one spectrum of $\mathcal{O}_K$, a Haar measure $\tau_v'$ on the $\sigma$-twisted centralizer of the base change [`AutomorphicForm.tensorPlace`](def/AutomorphicForm_BaseChangePlaces.html#L49) of $\delta$ in $\mathrm{GL}_2(L \otimes_K K_v)$ (hypotheses `τf'`, `hτf'`); and a constant $s \in [0,\infty]$.
--
--   The archimedean normalisation `harch` is stated for the $\mathbb{R}$-algebra structures on $K_\infty$ and on $L \otimes_K K_\infty$ obtained from $\mathbb{R} \to$ mixed space $\cong K_\infty$ followed by $K_\infty \to L \otimes_K K_\infty$, and for the Borel structure on $M_2(L \otimes_K K_\infty)$. It asserts the existence of $n_2 \in \mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\, n_2 \to M_2(L \otimes_K K_\infty)$ whose $\mathbb{R}$-span is exactly the set of $X$ with $X\,\delta_\infty = \delta_\infty\,\sigma(X)$, where $\delta_\infty$ is the matrix of the archimedean base change of $\delta$ and $\sigma$ is applied entrywise, and such that the pushforward of $\tau_\infty'$ along the inclusion of the twisted centralizer into $M_2(L \otimes_K K_\infty)$ equals $s$ times the following measure: the coordinate pushforward $(c_i) \mapsto \sum_i c_i e_2(i)$ of Lebesgue measure on $\mathrm{Fin}\,n_2 \to \mathbb{R}$, scaled by $\sqrt{|\det(\mathrm{Tr}_{(L\otimes_K K_\infty)/\mathbb{R}}\,\mathrm{tr}(e_2(i)e_2(j)))_{i,j}|}$, and taken with density $X \mapsto |N_{(L \otimes_K K_\infty)/\mathbb{R}}(\det X)|^{-1}$.
--
--   The finite normalisations involve a family $t : v \mapsto t_v \in [0,\infty]$ and a finite set $S_0$ of finite places with $t_v = 1$ for $v \notin S_0$ (hypothesis `ht`). The hypothesis `hfin` requires, for every finite place $v$, one of two alternatives. First alternative: there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ which is a norm conjugator in the sense of [`AutomorphicForm.IsNormConjugator`](def/AutomorphicForm_TwistedOrbital.html#L214), namely the base change to $L \otimes_K K_v$ of the $v$-component of the scalar matrix $\mathrm{diag}(u,u)$ equals $y^{-1}$ times the norm string of the base change of $\delta$ at $v$ times $y$, and the pushforward of $\tau_v'$ along $t \mapsto y^{-1} t y$ equals $t_v$ times the pushforward along [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) of the local Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$, the Haar measure giving mass one to the compact open set of matrices which together with their inverses have entries in $\mathcal{O}_v$. Second alternative: no unit $z$ of $L \otimes_K K_v$ makes the scalar matrix with entry $z$ $\sigma$-conjugate to the base change of $\delta$ at $v$, in the sense of [`AutomorphicForm.IsSigmaConjugate`](def/AutomorphicForm_TwistedOrbital.html#L208) (that is, $\delta' = x^{-1}\delta\,\sigma(x)$ for some $x$), and, writing $m_v$ for the $\tau_v'$-measure of the set of $t$ in the twisted centralizer whose determinant is the image under $K_v \to L \otimes_K K_v$ of a unit $s$ of $K_v$ with $|s|_v = 1$, one has $m_v \cdot N(v) = t_v + m_v$, where $N(v)$ is the absolute norm of the prime ideal of $v$.
--
--   The global measure data consist of a Haar measure $\tau'$ on the $\sigma$-twisted centralizer of $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ (hypotheses `τ'`, `hτ'`) and a real constant $c_{\tau'} > 0$ (hypotheses `cτ'`, `hcτ'`), subject to the Euler-factorisation hypothesis `hτ'prod`: for every finite set $S$ of finite places containing $S_0$ and all complex-valued functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_\infty$ on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and $W_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$, such that $W_\infty$ is almost everywhere strongly measurable on the archimedean twisted centralizer for $\tau_\infty'$, each $W_v$ with $v \in S$ is almost everywhere strongly measurable on the twisted centralizer at $v$ for $\tau_v'$, and such that $W(t) = W_\infty(t_\infty) \prod_{v \in S} W_v(t_v)$ for every $t$ in the adelic twisted centralizer whose base change at every $v \notin S$ lies in the semi-local integral set [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (those elements which, together with their inverses, have entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$ under `HeightOneSpectrum.tensorAdicCompletionIntegersTo`), while $W(t) = 0$ whenever the base change of $t$ at some $v \notin S$ fails to lie in that set, one has $\int W \, d\tau' = c_{\tau'} \cdot \bigl(\int W_\infty \, d\tau_\infty'\bigr) \cdot \prod_{v \in S} \int W_v \, d\tau_v'$.
--
--   Finally, a nonzero vector $v \in L^2$ is fixed (hypotheses `v`, `hv`), and $\mathbb{A}_L$ is equipped with a Borel measurable structure and an additive Haar measure $\mu_1$ normalised by $\mu_1(\mathrm{adelicBox}\, L) = 1$, the adelic box being the set of adeles whose archimedean part lies in the fundamental domain of the lattice basis of the mixed space of $L$ and whose finite part is integral at every place.
--
--   Under these hypotheses, there exists a set $U \subseteq (\mathrm{Fin}\,2 \to \mathbb{A}_{L,\mathrm{fin}})$ of finite-adelic column vectors which is open, compact and nonempty, such that for every Schwartz function $g \in \mathcal{S}((\mathrm{Fin}\,2 \to \text{mixed space of } L), \mathbb{C})$ with compact support and with $\mathrm{Re}\,g(y) \ge 0$ and $\mathrm{Im}\,g(y) = 0$ for all $y$, the following holds. Write $\psi$ for the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ given by `Algebra.TensorProduct.comm` followed by [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), and for $t$ in the adelic twisted centralizer let $\psi(t) \in \mathrm{GL}_2(\mathbb{A}_L)$ be the entrywise image of $t$ and $\psi(t)\cdot v$ the column vector obtained by applying $\psi(t)$ to the image of $v$ under $L \to \mathbb{A}_L$. Then, as $s \to 1$ from above (along the neighbourhood filter of $1$ within $(1,\infty)$), the real-parametrised quantity
--   $$\mathrm{ofReal}(s-1) \cdot \int^{-} \mathrm{ofReal}\Bigl(\mathrm{Re}\bigl[g\bigl((\psi(t)\cdot v)_{i,\infty}\bigr)\cdot \mathbf{1}_U\bigl((\psi(t)\cdot v)_{i,\mathrm{fin}}\bigr)\bigr]\Bigr) \cdot \mathrm{ofReal}\bigl(\|\det \psi(t)\|_{\mathbb{A}_L}^{\,s}\bigr)\, d\tau'(t)$$
--   tends to
--   $$2^{-1}\cdot\Bigl(\int^{-} \mathrm{ofReal}\bigl(\mathrm{Re}[g((x_i)_\infty)\cdot \mathbf{1}_U((x_i)_{\mathrm{fin}})]\bigr)\, d(\mathrm{pairHaar}\,\mu_1)(x)\Bigr)\cdot\Bigl(\mathrm{ofReal}(c_{\tau'})\cdot s\cdot 2^{2\,[K:\mathbb{Q}]}\cdot\prod_{v \in S_0} t_v \cdot \mathrm{ofReal}\bigl(d_K^2\cdot \mathrm{Re}\,\zeta_K(2)\cdot \rho_K\bigr)\Bigr).$$
--   Here the lower integrals are Lebesgue integrals of $[0,\infty]$-valued functions, the archimedean components of adelic vectors are transported to the mixed space by `InfiniteAdeleRing.ringEquiv_mixedSpace L`, $\mathbf{1}_U$ is the complex-valued indicator of $U$, $\|\cdot\|_{\mathbb{A}_L}$ is the idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) given by the distributive Haar character of $\mathbb{A}_L$, `pairHaar` $\mu_1$ is the product measure $\mu_1 \times \mu_1$ on $\mathrm{Fin}\,2 \to \mathbb{A}_L$, $d_K$ is the discriminant of $K$, $\zeta_K$ the Dedekind zeta function of $K$ and $\rho_K$ its residue `NumberField.dedekindZeta_residue K`. The constant $s$ occurring in the limit value is the $[0,\infty]$-valued parameter of the archimedean normalisation `harch`, not the real variable of the limit, which is bound in the function whose limit is taken.
--
--   This is the Euler-product half of the residue computation at $s = 1$ for the adelic zeta integral of the quaternion algebra realised as the $\sigma$-twisted centralizer of $\delta$, evaluated on the standard test functions attached to a level structure adapted to the given local normalisations (a Schwartz function at the archimedean places times the indicator of a compact open set of finite-adelic columns). It combines the factorisation of the $\tau'$-integral, the local normalisations at the archimedean and finite places, and the existence of a suitable level set $U$, and is used to produce a Schwartz–Bruhat test function with the same residue behaviour in [`AutomorphicForm.exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two.lean

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

theorem AutomorphicForm.exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two
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
    ∃ U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L), IsOpen U ∧ IsCompact U ∧ U.Nonempty ∧
    ∀ (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ)), HasCompactSupport g →
      (∀ y, 0 ≤ (g y).re ∧ (g y).im = 0) →
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
