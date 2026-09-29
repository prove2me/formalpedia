-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub
-- name    : AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/43e367e1-0453-503e-a3fb-1da68fb80bb1
-- title:
--   Unfolding the unipotent term along centre, torus and trace
-- statement:
--   **Setting.** $K$ and $L$ are number fields with $L/K$ Galois, and $\mathbb{A}_K$, $\mathbb{A}_L$ denote their adele rings. The idele group $\mathbb{A}_L^\times$ carries a Borel measurable structure and a Haar measure $\nu_{Z_L}$; $\Omega_L\subseteq\mathbb{A}_L^\times$ is a set subject to `hΩL`, which asserts that $\Omega_L$ is a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z_L}$. Further data: a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism $\mathrm{Gal}(L/K)\to\operatorname{RingAut}(\mathbb{A}_L)$ whose value at each $g$ is continuous and extends the action of $g$ on $L$; an element $\sigma\in\mathrm{Gal}(L/K)$ with `hgen` asserting that every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$; and a homomorphism $\xi_L$ from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$. Write $\sigma_D$ for the ring automorphism $D.\mathrm{act}(\sigma)$ of $\mathbb{A}_L$, $\sigma_{D*}$ for its entrywise action [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) on $GL_2(\mathbb{A}_L)$, and again $\sigma_D$ for the induced automorphism [`M4aHerbrand.IdeleGaloisDescent.unitsAct D σ`](def/M4aHerbrand_IdeleClassVocab.html#L41) of $\mathbb{A}_L^\times$. Write $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ (`unipotentGL2`), $d(t)=\operatorname{diag}(t,1)$ (`diagOne`), $z(u)=u\,I_2$ (`centralScalar`), $\iota_*:GL_2(L)\to GL_2(\mathbb{A}_L)$ for the map induced by $L\to\mathbb{A}_L$ (`globalPoints`), $H=$ [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) for the adelic height (the product of the archimedean and finite local heights), $\|t\|=$ [`NumberField.TateGlobal.ideleNorm L t`](def/NumberField_TateGlobalZeta.html#L19) for the idele norm (the distributive Haar character), and $\mathbf{K}_L$ for the subgroup `adelicMaximalCompact L` equipped with the Haar measure `maximalCompactHaar L`.
--
--   **Hypotheses on the character and the test function.** `hξc`: the function $z\mapsto\xi_L(z)\in\mathbb{C}$ on $\mathbb{A}_L^\times$ is continuous. `hξt`: $\xi_L(z)=1$ for every $z$ in the image of $L^\times$. The function $\varphi:GL_2(\mathbb{A}_L)\to\mathbb{C}$ is continuous (`hφc`) and has compact support (`hφs`), and $R$ is a real number.
--
--   **Fundamental-domain hypotheses.** $X\subseteq\mathbb{A}_L$, and $\Omega_2,\Omega_{2K}\subseteq\mathbb{A}_L^\times$ satisfy: `hX`, that $X$ is an additive fundamental domain for the principal subgroup $L\subseteq\mathbb{A}_L$ with respect to the adelic additive Haar measure `adelicAddHaar (𝓞 L) L`; `hΩ₂`, that $\Omega_2$ is a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to the idelic Haar measure [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391); `hΩ₂Km`, that $\Omega_{2K}$ is measurable; and `hΩ₂K`, that $\Omega_{2K}$ is a fundamental domain, again for the idelic Haar measure, for the range of the composite of $K^\times\to\mathbb{A}_K^\times$ with the base-change map [`AutomorphicForm.TransversalMeasure.idelesBaseChange K L`](def/AutomorphicForm_TransversalMeasure.html#L85) (the map on units induced by the ring homomorphism [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14) $:\mathbb{A}_K\to\mathbb{A}_L$), that is, for the image of $K^\times$ in $\mathbb{A}_L^\times$.
--
--   **Hypotheses on the base measure and the trace fibration.** $\mathbb{A}_K$ is a Borel space, $\mu_K$ is an additive Haar measure on $\mathbb{A}_K$ normalised by `hμK1` so that the adelic box [`NumberField.AdelicBox.adelicBox K`](def/NumberField_AdelicBox.html#L295) has mass $1$, and $c\in[0,\infty]$ satisfies $c\neq 0$ (`hc0`), $c\neq\infty$ (`hcT`) and `hc`: for every measurable $G:\mathbb{A}_L\to[0,\infty]$,
--   $$\int_{\mathbb{A}_L} G \,d(\text{adelicAddHaar})\;=\;c\int_{\mathbb{A}_K}\int_{(\mathbb{A}_K)^{m}} G\big(\mathrm{traceFibre}_{K,L}(r,w)\big)\,dw\,d\mu_K(r),$$
--   where $m=\operatorname{rank}_K\ker(\mathrm{Tr}_{L/K})$, the inner measure is the $m$-fold product of `adelicAddHaar (𝓞 K) K`, and $\mathrm{traceFibre}_{K,L}(r,w)=\beta(r)\,[L:K]^{-1}+\sum_i\beta(w_i)\,e_i$ with $\beta=$ [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14), the elements $[L:K]^{-1}$ and $e_i$ being taken in $\mathbb{A}_L$ via $L\to\mathbb{A}_L$ and $(e_i)_i$ being the basis `Module.finBasis K (LinearMap.ker (Algebra.trace K L))`. For $F:\mathbb{A}_L\to\mathbb{C}$ the trace push-forward is $\widehat F(r)=\int_{(\mathbb{A}_K)^m}F(\mathrm{traceFibre}_{K,L}(r,w))\,dw$ (`tracePushforward`).
--
--   **The finiteness hypothesis `hfin`.** Writing $g=n(x)d(t)k$, it is assumed that
--   $$\int^-_{x\in X}\int^-_{t\in\Omega_2}\int^-_{k\in\mathbf{K}_L}\Big(\int^-_{z\in\Omega_L}\|\xi_L(z)\|_e\sum_{s\in L^\times}\;\sum_{\substack{a\in L^\times\\ N_{L/K}(a)=1}}\big\|T_{s,a}(x,t,k,z)\big\|_e\,d\nu_{Z_L}(z)\Big)\cdot\|t\|^{-1}\,dk\,dt\,dx\;\neq\;\infty,$$
--   where $T_{s,a}(x,t,k,z)$ is the difference of
--   $$\sum^{\flat}_{\delta}\varphi\big(g^{-1}\,\iota_*(\delta)\,\sigma_{D*}(z(z)\,g)\big),\qquad \delta\in \mathrm{normUnipotentSet}_{K,L}(\sigma,\mathrm{hgen}),\ \delta_{10}=0,\ \delta_{11}=s,\ \delta_{00}=sa,$$
--   and of the value at $z(z)g$ of the indicator of the high set $\{h: e^R<H(h)\}$ applied to the constant-term function
--   $$h\;\longmapsto\;\int_{\mathbb{A}_L}\Big(\sum^{\flat}_{\delta_{10}=0,\ \delta_{11}=s,\ \delta_{00}=sa}\varphi\big(g^{-1}\,\iota_*(\delta)\,\sigma_{D*}(n(q)\,h)\big)\Big)\,d\mathbb{P}(q),$$
--   $\mathbb{P}$ being the adelic additive Haar measure conditioned on the adelic box `adelicBox L`. Here $\sum^{\flat}$ is the finite-support sum over the indicated set of $\delta\in GL_2(L)$, the first set being cut out inside `TwistedBruhat.normUnipotentSet K L σ hgen`, namely the set of $\delta$ whose $\sigma$-conjugacy class has norm class (under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766)) equal to the conjugacy class of some $\gamma\in GL_2(K)$ of unipotent type, while the second set carries no such condition.
--
--   **Conclusion.** Put, for $t\in\mathbb{A}_L^\times$, $k\in\mathbf{K}_L$ and $\zeta\in\mathbb{A}_L^\times$,
--   $$G_{t,k,\zeta}(w)=\varphi\big(k^{-1}\,n(w\,t^{-1})\,d(\sigma_D t\cdot t^{-1})\,z(\sigma_D\zeta)\,\sigma_{D*}(k)\big)\qquad(w\in\mathbb{A}_L),$$
--   and
--   $$A(t,k,\zeta)=\sum^{\flat}_{\eta\in K^\times}\widehat{G_{t,k,\zeta}}\big(\eta\big)\;-\;\begin{cases}\displaystyle\int_{\mathbb{A}_K}\widehat{G_{t,k,\zeta}}(r)\,d\mu_K(r),&e^R<H\big(d(t)\big),\\[2pt]0,&\text{otherwise,}\end{cases}$$
--   the argument $\eta$ of the first term being taken in $\mathbb{A}_K$ via $K\to\mathbb{A}_K$ and the sum over $\eta$ being a finite-support sum over all of $K^\times$. Then two assertions hold.
--
--   (i) The iterated lower integral
--   $$\int^-_{t\in\Omega_{2K}}\int^-_{k\in\mathbf{K}_L}\int^-_{\zeta\in\mathbb{A}_L^\times}\|\xi_L(\zeta)\|_e\,\|A(t,k,\zeta)\|_e\,\|t\|^{-1}\,d\nu_{Z_L}(\zeta)\,dk\,dt$$
--   is not $\infty$, the integrations in $t$ and $k$ being with respect to the idelic Haar measure on $\mathbb{A}_L^\times$ and `maximalCompactHaar L`.
--
--   (ii) The Bochner integrals satisfy
--   $$\int_{X}\int_{\Omega_2}\int_{\mathbf{K}_L}\Big(\int_{\Omega_L}\xi_L(z)\big(\mathcal{K}(z,n(x)d(t)k)-\mathcal{K}_R(z,n(x)d(t)k)\big)\,d\nu_{Z_L}(z)\Big)\|t\|^{-1}\,dk\,dt\,dx$$
--   $$=\;c_{\mathbb{R}}\int_{\Omega_{2K}}\int_{\mathbf{K}_L}\Big(\int_{\mathbb{A}_L^\times}\xi_L(\zeta)\,A(t,k,\zeta)\,d\nu_{Z_L}(\zeta)\Big)\|t\|^{-1}\,dk\,dt,$$
--   where $c_{\mathbb{R}}$ is the real number $c$ regarded as a complex number, the outer integrals on the left are over the additive fundamental domain $X$ with respect to the adelic additive Haar measure and over $\Omega_2$ with respect to the idelic Haar measure, $\mathcal{K}=$ `TwistedBruhat.cuspKernel K L D σ hgen φ` is
--   $$\mathcal{K}(z,g)=\sum^{\flat}_{\beta}\varphi\big(g^{-1}\,\iota_*(\beta)\,\sigma_{D*}(z(z)g)\big),\qquad \beta\in\mathrm{normUnipotentSet}_{K,L}(\sigma,\mathrm{hgen})\cap\{\beta_{10}=0\},$$
--   and $\mathcal{K}_R=$ `TwistedBruhat.cuspTruncation K L D σ R φ` is the value at $z(z)g$ of the indicator of $\{h:e^R<H(h)\}$ applied to
--   $$h\;\longmapsto\;\int_{\mathbb{A}_L}\Big(\sum^{\flat}_{\delta\in\mathrm{borelNormOneSet}_{K,L}}\varphi\big(g^{-1}\,\iota_*(\delta)\,\sigma_{D*}(n(q)h)\big)\Big)\,d\mathbb{P}(q),$$
--   with $\mathrm{borelNormOneSet}_{K,L}=\{\delta\in GL_2(L):\delta_{10}=0,\ N_{L/K}(\delta_{00}/\delta_{11})=1\}$ and $\mathbb{P}$ as above. In particular the right-hand side involves no integration over $X$, and the sums over $s\in L^\times$ and over the norm-one units have disappeared in favour of the full idele integral in $\zeta$, the fundamental domain $\Omega_{2K}$ for $K^\times$, and the sum over $\eta\in K^\times$ of the trace push-forward.
--
--   This is the unfolding step for the unipotent-type contribution to the twisted (base-change) trace formula for $GL_2$ over a cyclic extension $L/K$: the sum over lower-right entries is unfolded against the centre, the norm-one diagonal ratios against the torus, and the unipotent lattice along the trace fibration of $\mathbb{A}_L$ over $\mathbb{A}_K$, the truncation being carried along. It is used by [`AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2`](thm.html#AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2), and it is proved from the three preceding unfolding lemmas for the same integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₂ Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure] (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫⁻ t in Ω₂K, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ * ‖((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂νZL ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) ∧
    (∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) - TwistedBruhat.cuspTruncation K L D σ R φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) =
      (c.toReal : ℂ) * ∫ t in Ω₂K, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) := by sorry
