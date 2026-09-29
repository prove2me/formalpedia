-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise
-- name    : AutomorphicForm.TwistedBruhat.integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/f2e0623c-26b3-545a-8a60-06644b9a005b
-- title:
--   Fibrewise collapse of the twisted cusp kernel Iwasawa integral
-- statement:
--   The data are: number fields $K$ and $L$ with $L/K$ Galois; a Borel measurable structure on the idele unit group $(\mathbb{A}_L)^\times$ of $L$; a Haar measure $\nu_{Z_L}$ on $(\mathbb{A}_L)^\times$; and a set $\Omega_L\subseteq(\mathbb{A}_L)^\times$ which, by the hypothesis `hΩL`, is a fundamental domain for the action of the image of $L^\times$ under $\mathrm{Units.map}$ of $L\to\mathbb{A}_L$ on $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z_L}$. The Galois data consist of an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) $D$ for $\mathcal{O}_L$, $K$, $L$, that is a homomorphism $D.\mathrm{act}$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with the diagonal embedding of $L$ and continuous in each argument, together with an element $\sigma\in\mathrm{Gal}(L/K)$ and the hypothesis `hgen` that every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$. The character data consist of a homomorphism $\xi_L$ from the top subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$, subject to `hξc`, continuity of $z\mapsto\xi_L(z)$ as a complex-valued function, and `hξt`, triviality of $\xi_L$ on the image of $L^\times$ in $(\mathbb{A}_L)^\times$. The test function is $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$, continuous (`hφc`) and of compact support (`hφs`). Finally there are a truncation parameter $R\in\mathbb{R}$, a set $X\subseteq\mathbb{A}_L$ and a set $\Omega_2\subseteq(\mathbb{A}_L)^\times$ over which the outer integrations are restricted.
--
--   Notation for the blocks occurring in the integrands: for $x\in\mathbb{A}_L$, $t\in(\mathbb{A}_L)^\times$ and $k$ in the adelic maximal compact subgroup (the elements whose finite part is integral and whose archimedean components are row isometries at every infinite place), write $g=n(x)\,\mathrm{diag}(t,1)\,k$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\mathrm{diag}(t,1)$ is the diagonal matrix with entries $t,1$; $\iota$ denotes the map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$ induced by $L\to\mathbb{A}_L$; $z(\cdot)$ denotes the central scalar embedding $(\mathbb{A}_L)^\times\to\mathrm{GL}_2(\mathbb{A}_L)$; $\sigma_D$ denotes the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}(\sigma)$ entrywise; $\|t\|$ denotes the idele norm of $t$, the value of the distributive Haar character of $\mathbb{A}_L$ at $t$; the set $\mathrm{normUnipotentSet}$ consists of those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma$-twisted norm class, under the map [`LT.TwistedNorm.normClassMap`](def/TwistedNormClasses.html#L766) attached to `hgen`, is the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ of unipotent type; the `highSet` of the adelic height $H$ (the product of the archimedean and finite local heights) at level $e^R$ is $\{g:e^R<H(g)\}$; and for a measure $\mu$ the constant term of a function $f$ along the unipotent family $q\mapsto n(q)$ is $g\mapsto\int f(n(q)g)\,d\mu(q)$, the measure used throughout being the additive adelic Haar measure on $\mathbb{A}_L$ conditioned on the adelic box (infinite part in the fundamental parallelotope of the lattice basis, finite part everywhere integral). With these, $\mathrm{cuspKernel}$ at $(z,g)$ is the finitely supported sum of $\varphi\bigl(g^{-1}\iota(\beta)\,\sigma_D(z(z)g)\bigr)$ over $\beta$ in the intersection of $\mathrm{normUnipotentSet}$ with the Borel subgroup $\{\beta_{10}=0\}$ of $\mathrm{GL}_2(L)$, and $\mathrm{cuspTruncation}$ at $(z,g)$ is the indicator function of the high set of the adelic height at level $e^R$, applied to the constant term of $y\mapsto\sum_{\delta}\varphi\bigl(g^{-1}\iota(\delta)\,\sigma_D(y)\bigr)$, the sum being over $\delta\in\mathrm{GL}_2(L)$ with $\delta_{10}=0$ and $N_{L/K}(\delta_{00}/\delta_{11})=1$, and evaluated at $z(z)g$.
--
--   The hypothesis `hfin` is a fibrewise absolute-convergence assumption: the iterated lower Lebesgue integral over $x\in X$ (additive adelic Haar), $t\in\Omega_2$ (idelic Haar) and $k$ over the whole maximal compact subgroup (its Haar measure) of
--   $$\Bigl(\int^-_{z\in\Omega_L}\|\xi_L(z)\|_e\sum_{s\in L^\times}\ \sum_{a\in\{\alpha\in L^\times:\,N_{L/K}(\alpha)=1\}}\bigl\|\,\Sigma_{s,a}(x,t,k,z)-T_{s,a}(x,t,k,z)\,\bigr\|_e\,d\nu_{Z_L}\Bigr)\cdot\mathrm{ofReal}\,\|t\|^{-1}$$
--   is not $\top$, where $\Sigma_{s,a}$ is the finitely supported sum of $\varphi\bigl(g^{-1}\iota(\delta)\,\sigma_D(z(z)g)\bigr)$ over those $\delta\in\mathrm{normUnipotentSet}$ with $\delta_{10}=0$, $\delta_{11}=s$ and $\delta_{00}=sa$, and $T_{s,a}$ is the indicator of the high set of the adelic height at level $e^R$ applied to the constant term of $y\mapsto\sum_\delta\varphi\bigl(g^{-1}\iota(\delta)\,\sigma_D(y)\bigr)$, this last sum running over the $\delta\in\mathrm{GL}_2(L)$ with $\delta_{10}=0$, $\delta_{11}=s$, $\delta_{00}=sa$ only (no condition of lying in $\mathrm{normUnipotentSet}$), and evaluated at $z(z)g$; the sums over $s$ and $a$ are unconditional sums in $[0,\infty]$, and $\|\cdot\|_e$ is the extended-real norm.
--
--   The conclusion is a conjunction of two assertions. First, the Bochner-integral identity
--   $$\int_{x\in X}\int_{t\in\Omega_2}\int_k\Bigl(\int_{z\in\Omega_L}\xi_L(z)\bigl(\mathrm{cuspKernel}(z,g)-\mathrm{cuspTruncation}(z,g)\bigr)d\nu_{Z_L}\Bigr)\,\|t\|^{-1}$$
--   $$=\int_{x\in X}\int_{t\in\Omega_2}\int_k\Bigl(\int_{\zeta}\xi_L(\zeta)\sum_{a\in\{\alpha\in L^\times:\,N_{L/K}(\alpha)=1\}}\bigl(\Sigma_{1,a}(x,t,k,\zeta)-T_{1,a}(x,t,k,\zeta)\bigr)d\nu_{Z_L}\Bigr)\,\|t\|^{-1},$$
--   where on the right the inner integral is over the whole of $(\mathbb{A}_L)^\times$ against $\nu_{Z_L}$, the sum over $a$ is a complex unconditional sum over the subtype of norm-one units, $\Sigma_{1,a}$ is the finitely supported sum of $\varphi\bigl(g^{-1}\iota(\delta)\,\sigma_D(z(\zeta)g)\bigr)$ over those $\delta\in\mathrm{normUnipotentSet}$ with $\delta_{10}=0$, $\delta_{11}=1$, $\delta_{00}=a$, and $T_{1,a}$ is the indicator of the high set of the adelic height at level $e^R$ applied, at $z(\zeta)g$, to the constant term of $y\mapsto\sum_\delta\varphi\bigl(g^{-1}\iota(\delta)\,\sigma_D(y)\bigr)$ with $\delta$ running over the $\delta\in\mathrm{GL}_2(L)$ satisfying $\delta_{10}=0$, $\delta_{11}=1$, $\delta_{00}=a$; all three outer integrations are as in `hfin`, the $x$-integral restricted to $X$ against the additive adelic Haar measure, the $t$-integral restricted to $\Omega_2$ against the idelic Haar measure and the $k$-integral over the whole maximal compact subgroup against its Haar measure, and the scalar factor is the complex number attached to the real $\|t\|^{-1}$.
--
--   Secondly, the corresponding absolute integral of the right-hand integrand is finite: the iterated lower Lebesgue integral over $x\in X$, $t\in\Omega_2$ and $k$ of
--   $$\Bigl(\int^-_{\zeta}\|\xi_L(\zeta)\|_e\sum_{a\in\{\alpha\in L^\times:\,N_{L/K}(\alpha)=1\}}\bigl\|\Sigma_{1,a}(x,t,k,\zeta)-T_{1,a}(x,t,k,\zeta)\bigr\|_e\,d\nu_{Z_L}\Bigr)\cdot\mathrm{ofReal}\,\|t\|^{-1}$$
--   is not $\top$, the inner integral again being over all of $(\mathbb{A}_L)^\times$ and the norms being taken inside the sum over $a$.
--
--   This is the step in the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$ at which the sum over $s\in L^\times$ and the integration over a fundamental domain $\Omega_L$ for $L^\times$ in the ideles are traded, using the invariance of $\xi_L$ on principal ideles, for a single integration over the full idele class group with the fibre $\delta_{11}=1$, $\delta_{00}=a$ and $N_{L/K}(a)=1$. It is used by [`AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub), where the resulting expression is matched with the trace pushforward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise.lean

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

theorem AutomorphicForm.TwistedBruhat.integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
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
    (∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) - TwistedBruhat.cuspTruncation K L D σ R φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      ∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) ∧
    (∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) := by sorry
