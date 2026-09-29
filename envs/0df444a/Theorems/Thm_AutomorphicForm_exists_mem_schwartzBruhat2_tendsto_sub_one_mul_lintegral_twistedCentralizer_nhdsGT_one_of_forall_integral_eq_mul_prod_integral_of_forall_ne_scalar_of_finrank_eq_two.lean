-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/db293f36-08f4-523a-b260-7ada04816046
-- title:
--   Test function with prescribed residue of a twisted orbital zeta integral
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an extension of $K$, the hypothesis `h2` asserting $[L:K]=2$, and $\sigma$ is a $K$-automorphism of $L$ which by `hgen` generates the whole automorphism group (every $\tau$ lies in the subgroup of integral powers of $\sigma$). Fixed data are $\delta_0\in\mathrm{GL}_2(L)$, a unit $c$ of $L\otimes_K\mathbb A_K$ and a unit $u$ of $\mathbb A_K$, and the element
--   $$\delta\;=\;\bigl(\delta_0\otimes 1\bigr)\cdot c\,I\;\in\;\mathrm{GL}_2\bigl(L\otimes_K\mathbb A_K\bigr),$$
--   the product of the image of $\delta_0$ under the left inclusion $L\to L\otimes_K\mathbb A_K$ with the scalar matrix of $c$. For a $K$-algebra $A$, `sigmaTensor` is the ring endomorphism $\sigma\otimes\mathrm{id}$ of $L\otimes_K A$, `sigmaGL` is its entrywise action $x\mapsto x^\sigma$ on $\mathrm{GL}_2(L\otimes_K A)$, the norm string of an element is $\prod_{i<[L:K]}\bigl(x^{\sigma}\bigr)^{(i)}$ (the product of the first $[L:K]$ iterates of `sigmaGL` applied to it, in order), and the $\sigma$-twisted centralizer of $x$ is the subgroup $\{t : t\,x\,(t^{\sigma})^{-1}=x\}$. All general linear groups, matrix algebras and twisted centralizers occurring below carry their Borel $\sigma$-algebras.
--
--   Two hypotheses constrain $\delta$: `hN` asserts that the norm string of $\delta$ equals the image under `toTensorGL` (the map induced by the right inclusion $\mathbb A_K\to L\otimes_K\mathbb A_K$) of the scalar matrix of $u$; `hns` asserts that for every $x\in\mathrm{GL}_2(L)$ and every $z\in L^{\times}$ one has $x^{-1}\delta_0\,\sigma(x)\neq z\,I$, $\sigma$ acting entrywise — no $\sigma$-twisted conjugate of $\delta_0$ over $L$ is a scalar matrix.
--
--   Local measures. $\tau_a'$ is a Haar measure (`hτa'`) on the $\sigma$-twisted centralizer of the archimedean component `tensorArch` $\delta$ in $\mathrm{GL}_2(L\otimes_K K_\infty)$, where $K_\infty$ is the infinite adele ring of $K$; for each finite place $v$ of $K$, $\tau_f'(v)$ is a Haar measure (`hτf'`) on the $\sigma$-twisted centralizer of the local component `tensorPlace` $\delta$ in $\mathrm{GL}_2(L\otimes_K K_v)$.
--
--   The archimedean normalisation `harch`, in which $\mathbb R$ acts on $K_\infty$ through the identification with the mixed space and on $L\otimes_K K_\infty$ through the right inclusion, involves a constant $s\in[0,\infty]$ and asserts the existence of $n_2\in\mathbb N$ and an $\mathbb R$-linearly independent family $e_2:\mathrm{Fin}\,n_2\to M_2(L\otimes_K K_\infty)$ whose $\mathbb R$-span is exactly the set of $X$ with $X\,\delta_\infty=\delta_\infty\,X^{\sigma}$ ($\sigma$ applied entrywise, $\delta_\infty=$ `tensorArch` $\delta$), and such that the pushforward of $\tau_a'$ along the inclusion of the twisted centralizer into $M_2(L\otimes_K K_\infty)$ equals
--   $$s\cdot\Bigl[\;\sqrt{\bigl|\det\bigl(\mathrm{Tr}_{(L\otimes_K K_\infty)/\mathbb R}\,\mathrm{tr}(e_2(i)e_2(j))\bigr)_{i,j}\bigr|}\;\cdot\;\bigl(\text{Lebesgue measure pushed forward along }(c_i)\mapsto\textstyle\sum_i c_i\,e_2(i)\bigr)\Bigr]\;\text{with density}\;X\mapsto \bigl|N_{(L\otimes_K K_\infty)/\mathbb R}(\det X)\bigr|^{-1}.$$
--
--   The finite normalisation involves a family of factors $t_v\in[0,\infty]$ indexed by the finite places, a finite set $S_0$ of finite places with $t_v=1$ for $v\notin S_0$ (`ht`), and the dichotomy `hfin`: for every finite place $v$ of $K$, either
--   (i) there is $y\in\mathrm{GL}_2(L\otimes_K K_v)$ which is a norm conjugator, i.e. the image under `toTensorGL` of the scalar matrix of $u_v$ (the $v$-component of the finite part of the scalar matrix of $u$) equals $y^{-1}\cdot(\text{norm string of }\delta_v)\cdot y$, and the pushforward of $\tau_f'(v)$ along $t\mapsto y^{-1}ty$ equals $t_v$ times the pushforward along `toTensorGL` of the Haar measure `localHaar K v` on $\mathrm{GL}_2(K_v)$ attached to the positive compact `localIntegralCompacts K v` (hence of total mass one on it); or
--   (ii) no scalar matrix $z\,I$, $z\in(L\otimes_K K_v)^{\times}$, is $\sigma$-conjugate to $\delta_v$ (there is no $x$ with $z\,I=x^{-1}\delta_v x^{\sigma}$), and, writing $A_v$ for the set of elements $t$ of the twisted centralizer whose determinant is the image under the right inclusion $K_v\to L\otimes_K K_v$ of some $s\in K_v^{\times}$ with $|s|_v=1$, one has $\tau_f'(v)(A_v)\cdot N(v)=t_v+\tau_f'(v)(A_v)$, where $N(v)$ is the absolute norm of the prime $v$.
--
--   Globally, $\tau'$ is a Haar measure (`hτ'`) on the $\sigma$-twisted centralizer of $\delta$ in $\mathrm{GL}_2(L\otimes_K\mathbb A_K)$, and $c_{\tau'}>0$ is a real constant for which the factorisation hypothesis `hτ'prod` holds: for every finite set $S$ of finite places containing $S_0$ and all functions $W$ on the global twisted centralizer, $W_a$ on the archimedean one and $W_S(v)$ on the local ones, if $W_a$ is a.e. strongly measurable for $\tau_a'$, each $W_S(v)$ ($v\in S$) is a.e. strongly measurable for $\tau_f'(v)$, and $W$ satisfies $W(t)=W_a(\mathrm{tensorArch}\,t)\prod_{v\in S}W_S(v)(\mathrm{tensorPlace}_v\,t)$ whenever $\mathrm{tensorPlace}_v\,t$ lies in the semilocal integral units set `semiLocalIntegralSet K L v` for all $v\notin S$, and $W(t)=0$ as soon as $\mathrm{tensorPlace}_v\,t$ fails to lie in that set for some $v\notin S$, then
--   $$\int W\,d\tau'=c_{\tau'}\Bigl(\int W_a\,d\tau_a'\Bigr)\prod_{v\in S}\int W_S(v)\,d\tau_f'(v).$$
--
--   Finally, a nonzero vector $\mathbf v:\mathrm{Fin}\,2\to L$ is fixed (`hv`; the Lean binder is also named `v`, as is the running finite place), the adele ring $\mathbb A_L$ carries a Borel measurable structure, $\mu_1$ is an additive Haar measure on $\mathbb A_L$ normalised by $\mu_1(\mathrm{adelicBox}\,L)=1$ (`hμ₁`), and $\psi$ is an additive character of $\mathbb A_L$ with values in $\mathbb C$ which by `hψ` is global: trivial on the principal adeles $\mathrm{algebraMap}(L)$, continuous, and nontrivial.
--
--   Write $\mathrm{pairHaar}\,\mu_1$ for the product measure $\mu_1\times\mu_1$ on $\mathrm{Fin}\,2\to\mathbb A_L$, and for $t$ in the global twisted centralizer let
--   $$\mathrm{col}(t)\;=\;\iota(t)\cdot\bigl(\mathrm{algebraMap}_{L\to\mathbb A_L}\mathbf v_i\bigr)_i\in(\mathbb A_L)^2,\qquad \iota(t)\in M_2(\mathbb A_L),$$
--   where $\iota$ is induced entrywise by the ring isomorphism $L\otimes_K\mathbb A_K\cong\mathbb A_K\otimes_K L\cong\mathbb A_L$ (the commutation isomorphism followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57)), and let $N(t)=\mathrm{ideleNorm}_L(\det\iota(t))$, the module of $\det\iota(t)$ measured by the distributive Haar character of $\mathbb A_L$.
--
--   The conclusion asserts the existence of a function $\Phi:(\mathrm{Fin}\,2\to\mathbb A_L)\to\mathbb C$ such that:
--
--   (1) $\Phi$ lies in `schwartzBruhat2 L`, the $\mathbb C$-span of the pure tensors $x\mapsto g\bigl((x_i)_\infty\bigr)\,h\bigl((x_i)_{\mathrm{fin}}\bigr)$ with $g$ a Schwartz function on $(\text{mixed space of }L)^2$ and $h$ a locally constant, compactly supported function on $(\text{finite adeles of }L)^2$;
--
--   (2) $\mathrm{Re}\,\Phi(x)\geq 0$ and $\mathrm{Im}\,\Phi(x)=0$ for all $x$;
--
--   (3) $\int^{-}\mathrm{Re}\,\Phi\,d(\mathrm{pairHaar}\,\mu_1)\neq 0$;
--
--   (4) this same lower Lebesgue integral is $\neq\infty$;
--
--   (5) for every real $s_1>1$, $\displaystyle\int^{-}\mathrm{Re}\,\Phi(\mathrm{col}(t))\cdot N(t)^{s_1}\,d\tau'(t)<\infty$ (the real integrand being read in $[0,\infty]$ through `ENNReal.ofReal`);
--
--   (6) $\displaystyle\int^{-}_{\{t\,:\,1\le N(t)\}}\bigl\|\,\mathrm{reflectPair}\,\psi\,\mu_1\,\Phi(\mathrm{col}(t))\bigr\|\,d\tau'(t)<\infty$, where $\mathrm{reflectPair}\,\psi\,\mu_1\,\Phi$ is the Fourier transform of $\Phi$ with respect to the pair character built from $\psi$ and the measure $\mathrm{pairHaar}\,\mu_1$, evaluated at $(x_1,-x_0)$;
--
--   (7) as $s\to 1^{+}$,
--   $$(s-1)\int^{-}\mathrm{Re}\,\Phi(\mathrm{col}(t))\cdot N(t)^{s}\,d\tau'(t)\;\longrightarrow\;\frac12\Bigl(\int^{-}\mathrm{Re}\,\Phi\,d(\mathrm{pairHaar}\,\mu_1)\Bigr)\cdot\Bigl(c_{\tau'}\,s_{\mathrm{arch}}\,2^{2[K:\mathbb Q]}\Bigl(\prod_{v\in S_0}t_v\Bigr)\,\mathrm{disc}(K)^2\,\mathrm{Re}\,\zeta_K(2)\,\mathrm{res}_{s=1}\zeta_K\Bigr),$$
--   the limit being taken along the filter of right neighbourhoods of $1$ in $\mathbb R$ and the convergence being in $[0,\infty]$; here $s_{\mathrm{arch}}$ is the constant $s$ of `harch`, $\mathrm{disc}(K)$ the discriminant of $K$, $\zeta_K$ the Dedekind zeta function of $K$ and $\mathrm{res}_{s=1}\zeta_K$ its residue at $s=1$, the real factor $\mathrm{disc}(K)^2\,\mathrm{Re}\,\zeta_K(2)\,\mathrm{res}_{s=1}\zeta_K$ being transferred to $[0,\infty]$ by `ENNReal.ofReal`.
--
--   This is the Euler-product evaluation, for a suitably chosen standard factorisable test function, of the zeta integral over the $\sigma$-twisted centralizer of $\delta$ — the adelic unit group of the quaternion algebra attached to $\delta_0$ — together with the residue of that integral at $s=1$, in the local normalisations fixed by `harch` and `hfin`. It supplies the analytic input for [`AutomorphicForm.two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two), where the same constant is identified with a volume rate computed from fundamental domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two.lean

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
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two
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
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ) :
    ∃ Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ, Φ ∈ schwartzBruhat2 L ∧
      (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
      (∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) ≠ ⊤ ∧
      (∀ s₁ : ℝ, 1 < s₁ →
        ∫⁻ t, ENNReal.ofReal (Φ (((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s₁) ∂τ' < ⊤) ∧
      (∫⁻ t in {t | 1 ≤ NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))},
        ‖reflectPair ψ μ₁ Φ (((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))‖ₑ ∂τ' < ⊤) ∧
      Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        ∫⁻ t, ENNReal.ofReal (Φ (((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s) ∂τ')
        (𝓝[>] (1 : ℝ))
        (𝓝 (2⁻¹ * ((∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) *
          (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
            ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
              NumberField.dedekindZeta_residue K))))) := by sorry
