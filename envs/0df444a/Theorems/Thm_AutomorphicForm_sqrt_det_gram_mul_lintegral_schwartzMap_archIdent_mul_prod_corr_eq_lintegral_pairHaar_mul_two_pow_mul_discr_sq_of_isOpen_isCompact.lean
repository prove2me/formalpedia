-- Prove2me | Theorems.Thm_AutomorphicForm_sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_prod_corr_eq_lintegral_pairHaar_mul_two_pow_mul_discr_sq_of_isOpen_isCompact
-- name    : AutomorphicForm.sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_prod_corr_eq_lintegral_pairHaar_mul_two_pow_mul_discr_sq_of_isOpen_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9f256f9d-b606-5292-be06-d3f5b60b105b
-- title:
--   Covolume identity for the test function g⊗mathbf 1_U
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, `h2` requires $[L:K]=2$, $\sigma$ is a $K$-automorphism of $L$ and `hgen` requires every $K$-automorphism of $L$ to lie in the subgroup of integral powers of $\sigma$. Further data are $\delta_0\in\mathrm{GL}_2(L)$, a unit $c$ of $L\otimes_K\mathbb A_K$ and a unit $u$ of $\mathbb A_K$, where $\mathbb A_K=$ `AdeleRing (𝓞 K) K`. Write $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb A_K)$ for the product of the image of $\delta_0$ under the map induced by $\mathrm{includeLeftRingHom}:L\to L\otimes_K\mathbb A_K$ with the scalar matrix $cI$; write $\delta_\infty=$ `tensorArch K L` $\delta$ for its image under $\mathrm{id}_L\otimes(\mathbb A_K\to K_\infty)$ and $\delta_v=$ `tensorPlace K L v` $\delta$ for its image under $\mathrm{id}_L\otimes(\mathbb A_K\to K_v)$ at a height-one prime $v$ of $\mathcal O_K$. For a commutative $K$-algebra $A$, $\sigma$ acts on $L\otimes_K A$ by `sigmaTensor` $=\sigma\otimes\mathrm{id}_A$ and hence entrywise on matrices and on $\mathrm{GL}_2(L\otimes_K A)$ (`sigmaGL`, written $t\mapsto t^\sigma$); the twisted centralizer `twistedCentralizer K L A σ δ` is the subgroup $\{t:\ t\,\delta\,(t^\sigma)^{-1}=\delta\}$, and `normString K L A σ δ` is the product $\prod_{i<[L:K]}(\sigma_{\mathrm{GL}})^{i}(\delta)$. All general linear groups and twisted centralizers carry their Borel $\sigma$-algebras, and $\mathbb A_L$ is equipped with a measurable structure that is Borel.
--
--   The hypotheses on $\delta$ are: `hN`, that `normString` of $\delta$ equals the image of the scalar matrix $uI$ under `toTensorGL` (the map induced by $\mathbb A_K\to L\otimes_K\mathbb A_K$, $a\mapsto 1\otimes a$); and `hns`, that for no $x\in\mathrm{GL}_2(L)$ and $z\in L^\times$ is $x^{-1}\delta_0\,\sigma(x)$ the scalar matrix $zI$.
--
--   Measures on the local twisted centralizers: $\tau_a'$ is a measure on the twisted centralizer of $\delta_\infty$ in $\mathrm{GL}_2(L\otimes_K K_\infty)$, Haar by `hτa'`; for each height-one prime $v$ of $\mathcal O_K$, $\tau_f'(v)$ is a measure on the twisted centralizer of $\delta_v$ in $\mathrm{GL}_2(L\otimes_K K_v)$, Haar by `hτf'`.
--
--   A parameter $s\in[0,\infty]$ and the hypothesis `harch` describe $\tau_a'$: with $K_\infty$ and $L\otimes_K K_\infty$ made $\mathbb R$-algebras through the identification of $K_\infty$ with the mixed space of $K$ and through $a\mapsto1\otimes a$, and with $M_2(L\otimes_K K_\infty)$ given its Borel structure, there exist $n_2\in\mathbb N$ and an $\mathbb R$-linearly independent family $e_2:\mathrm{Fin}\,n_2\to M_2(L\otimes_K K_\infty)$ whose $\mathbb R$-span is the twisted commutant $\{X:\ X\delta_\infty=\delta_\infty X^\sigma\}$, such that the pushforward of $\tau_a'$ under the inclusion of the twisted centralizer of $\delta_\infty$ into $M_2(L\otimes_K K_\infty)$ equals $s$ times the measure obtained as follows: push Lebesgue measure on $\mathbb R^{n_2}$ forward along $cc\mapsto\sum_i cc_i\,e_{2,i}$, scale by $\sqrt{|\det(\mathrm{Tr}_{(L\otimes_K K_\infty)/\mathbb R}\,\mathrm{tr}(e_{2,i}e_{2,j}))_{i,j}|}$, and take the density $X\mapsto|N_{(L\otimes_K K_\infty)/\mathbb R}(\det X)|^{-1}$.
--
--   The local normalisation data consist of $t:\{\text{height-one primes of }\mathcal O_K\}\to[0,\infty]$, a finite set $S_0$ of such primes, `ht` ($t_v=1$ for $v\notin S_0$), and `hfin`, which requires for every $v$ one of two alternatives: either there is $y\in\mathrm{GL}_2(L\otimes_K K_v)$ with `IsNormConjugator`, i.e. the image under `toTensorGL` of the $v$-component of the scalar matrix $uI$ equals $y^{-1}\,\mathrm{normString}(\delta_v)\,y$, and the pushforward of $\tau_f'(v)$ under $t\mapsto y^{-1}ty$ equals $t_v$ times the pushforward under `toTensorGL` of the local Haar measure `localHaar K v` on $\mathrm{GL}_2(K_v)$ (normalised on the local integral set); or else $\delta_v$ is $\sigma$-conjugate to no scalar matrix over $L\otimes_K K_v$ and the $\tau_f'(v)$-measure $m_v$ of the set of $t$ in the twisted centralizer whose determinant is the image of some $s\in K_v^\times$ with $|s|_v=1$ satisfies $m_v\cdot\#(\mathcal O_K/v)=t_v+m_v$.
--
--   The global measure data are: a Haar measure $\tau'$ on the twisted centralizer of $\delta$ in $\mathrm{GL}_2(L\otimes_K\mathbb A_K)$, a real $c_{\tau'}>0$, and the factorisation hypothesis `hτ'prod`: for every finite set $S$ of primes with $S_0\subseteq S$ and all functions $W$ on $\mathrm{GL}_2(L\otimes_K\mathbb A_K)$, $W_a$ on $\mathrm{GL}_2(L\otimes_K K_\infty)$ and $W_S(v)$ on $\mathrm{GL}_2(L\otimes_K K_v)$ such that $W_a$ is almost everywhere strongly measurable on the archimedean twisted centralizer for $\tau_a'$, each $W_S(v)$ with $v\in S$ is almost everywhere strongly measurable for $\tau_f'(v)$, $W(t)=W_a(t_\infty)\prod_{v\in S}W_S(v)(t_v)$ for all $t$ in the global twisted centralizer whose component at each $v\notin S$ lies in `semiLocalIntegralSet K L v` (the set of $x\in\mathrm{GL}_2(L\otimes_K K_v)$ with all entries of $x$ and of $x^{-1}$ in `semiLocalIntegers K L v`, the image of $\mathcal O_L\otimes_{\mathcal O_K}\mathcal O_{K_v}$), and $W(t)=0$ whenever some component at $v\notin S$ fails to lie in that set, one has $\int W\,d\tau'=c_{\tau'}\bigl(\int W_a\,d\tau_a'\bigr)\prod_{v\in S}\int W_S(v)\,d\tau_f'(v)$.
--
--   The test data are: a nonzero vector in $L^2$, written `v` in the statement and denoted $\xi=(\xi_0,\xi_1)$ here to free the letter $v$ for primes; an additive Haar measure $\mu_1$ on $\mathbb A_L$ with $\mu_1$ of `adelicBox L` equal to $1$ (the box being the set of adeles whose infinite part lies in the preimage of the fundamental domain of the lattice basis of $L$ and whose finite part is integral at every place); a set $U\subseteq(\mathbb A_{L,f})^2$ which is open (`hUo`) and compact (`hUc`); and a Schwartz function $g$ on $\mathrm{Fin}\,2\to$ (mixed space of $L$) with values in $\mathbb C$, of compact support (`hg`) and with $g(y)$ real and non-negative for every $y$ (`hg'`).
--
--   The level data are: a finite set $S_1$ of primes with $S_0\subseteq S_1$ (`hS₁`); for each prime $v$ a subset $W(v)\subseteq\mathrm{GL}_2(L\otimes_K K_v)$, Borel measurable by `hWm`; `hW₀`, that for $v\notin S_1$ and every $x$ in the twisted centralizer of $\delta_v$, membership of $x$ in $W(v)$ is equivalent to all entries of $x$ lying in `semiLocalIntegers K L v`; and `hW₁`, that for every finite $S\supseteq S_1$ and every $t$ in the global twisted centralizer whose component at each $v\notin S$ lies in `semiLocalIntegralSet K L v`, the value at the finite part of the vector $\bigl(\mathrm{GL}_2(\mathbb A_L)\ni\ \bar t\bigr)\cdot(\xi_j)_j$ of the $\mathbb C$-valued indicator of $U$ equals $\prod_{v\in S}$ of the $\mathbb C$-valued indicator of $W(v)$ at the $v$-component of $t$; here $\bar t$ is the image of $t$ under the map induced by the ring isomorphism $L\otimes_K\mathbb A_K\cong\mathbb A_K\otimes_K L\cong\mathbb A_L$ (`Algebra.TensorProduct.comm` followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57)), the vector $(\xi_j)_j$ being pushed into $\mathbb A_L$ by the structure map. A further hypothesis `hunit` requires, for $v\notin S_1$, the existence of $y$ as in the first alternative of `hfin` (same `IsNormConjugator` condition) for which the pushforward of $\tau_f'(v)$ under $t\mapsto y^{-1}ty$ equals the pushforward of `localHaar K v` under `toTensorGL` exactly, with no factor $t_v$.
--
--   Finally, $\mathrm{Corr}$ assigns to each prime a function $\mathbb R\to[0,\infty]$, subject to `hCorr`: for $v\in S_1$ and every real $s'\ge1$,
--   $$\int_{\{t\,:\,t\in W(v)\}}\bigl\|N_{(L\otimes_K K_v)/K_v}(\det t)\bigr\|^{s'}\,d\tau_f'(v)=\mathrm{Corr}_v(s')\,\bigl(1-N(v)^{-2s'}\bigr)^{-1}\bigl(1-N(v)^{1-2s'}\bigr)^{-1},$$
--   the integral being a lower Lebesgue integral over the part of the twisted centralizer of $\delta_v$ lying in $W(v)$ and $N(v)$ the absolute norm of $v$; and `hCorr₁`: for $v\in S_1$, $\mathrm{Corr}_v(1)\neq\infty$ and $\mathrm{Corr}_v(s')\to\mathrm{Corr}_v(1)$ as $s'\to1^+$ from the right.
--
--   Conclusion. With the same $\mathbb R$-algebra structures on $K_\infty$ and $L\otimes_K K_\infty$ and the Borel structure on $M_2(L\otimes_K K_\infty)$ as in `harch`, for every $n_2\in\mathbb N$ and every $\mathbb R$-linearly independent family $e_2:\mathrm{Fin}\,n_2\to M_2(L\otimes_K K_\infty)$ whose $\mathbb R$-span equals the twisted commutant $\{X:\ X\delta_\infty=\delta_\infty X^\sigma\}$, the following identity of elements of $[0,\infty]$ holds:
--   $$\sqrt{\Bigl|\det\bigl(\mathrm{Tr}_{(L\otimes_K K_\infty)/\mathbb R}\,\mathrm{tr}(e_{2,i}e_{2,j})\bigr)_{i,j}\Bigr|}\ \cdot\int^{-}_{cc\in\mathbb R^{n_2}}\Bigl(g\bigl(i\mapsto \mathrm{archIdent}\bigl(((\textstyle\sum_k cc_k\,e_{2,k})\cdot(\xi_j\otimes1)_j)_i\bigr)\bigr)\Bigr)_{\mathrm{re}}\,dcc\ \cdot\prod_{v\in S_1}\mathrm{Corr}_v(1)$$
--   $$=\Bigl(\int^{-}_{x}\bigl(g(i\mapsto (x_i)_\infty)\cdot\mathbf 1_U\bigl(i\mapsto (x_i)_f\bigr)\bigr)_{\mathrm{re}}\,d(\mu_1\otimes\mu_1)\Bigr)\cdot 2^{2[K:\mathbb Q]}\cdot\Bigl(\prod_{v\in S_0}t_v\Bigr)\cdot d_K^{\,2}.$$
--   Here all integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions obtained by `ENNReal.ofReal` from the real part of the indicated complex value; `archIdent` is the ring homomorphism $L\otimes_K K_\infty\to\mathbb A_{L,\infty}$ followed, in both integrands, by the identification of $\mathbb A_{L,\infty}$ with the mixed space of $L$; $\mathbf 1_U$ is the indicator of $U$ with value $1\in\mathbb C$; $(x_i)_\infty$ and $(x_i)_f$ denote the infinite and finite components of the adele $x_i$; the measure on $\mathrm{Fin}\,2\to\mathbb A_L$ is `pairHaar μ₁`, the product of two copies of $\mu_1$; $[K:\mathbb Q]$ is the $\mathbb Q$-rank of $K$; and $d_K^{\,2}$ is `ENNReal.ofReal` of the square of the discriminant of $K$.
--
--   This is the covolume comparison that matches the archimedean integral of the test function $g$ over the twisted commutant, weighted by the square root of the Gram determinant of an $\mathbb R$-basis and by the finite correction factors $\mathrm{Corr}_v(1)$, against the global adelic integral of $g\otimes\mathbf 1_U$ over $\mathbb A_L^2$, with the explicit constant $2^{2[K:\mathbb Q]}\prod_{v\in S_0}t_v\,d_K^{\,2}$. It is used in the Euler-product limit statement [`AutomorphicForm.exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_isOpen_isCompact_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_finrank_eq_two), where twisted orbital integrals for the quadratic extension $L/K$ are evaluated in terms of Tamagawa-type volumes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_prod_corr_eq_lintegral_pairHaar_mul_two_pow_mul_discr_sq_of_isOpen_isCompact.lean

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

theorem AutomorphicForm.sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_prod_corr_eq_lintegral_pairHaar_mul_two_pow_mul_discr_sq_of_isOpen_isCompact
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
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U)
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
    (hCorr₁ : ∀ v ∈ S₁, Corr v 1 ≠ ⊤ ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1))) :
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
        2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) * ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2) := by sorry
