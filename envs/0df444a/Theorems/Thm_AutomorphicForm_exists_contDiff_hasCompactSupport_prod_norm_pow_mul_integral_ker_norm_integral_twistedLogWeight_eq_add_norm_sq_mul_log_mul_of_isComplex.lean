-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/30e0286f-75e6-56a0-9bee-f093c3ac6a00
-- title:
--   Twisted log-weight layer above a complex place of K
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite and Galois, $\sigma \in \mathrm{Gal}(L/K)$ is an automorphism such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$ (hypothesis `hgen`, so $\sigma$ generates the group), and $\ell := \operatorname{finrank}_K L$ is prime (hypothesis `hdeg`). Write $K_\infty =$ `InfiniteAdeleRing K` and $E = L \otimes_K K_\infty$. The measure-theoretic data are: measurable space structures on $E$ and on $E^\times$ which are the Borel structures of their topologies, an additive Haar measure $\lambda$ on $E$, and a Haar measure $\theta$ on the subgroup $U_1 := \ker\big(E^\times \to K_\infty^\times\big)$ obtained by applying `Units.map` to the norm $\mathrm{Alg\,norm}_{K_\infty} : E \to K_\infty$. The archimedean identification is $\iota_L :=$ `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L` $\circ$ [`AutomorphicForm.archIdent K L`](def/AutomorphicForm_TwistedOrbital.html#L420), where `archIdent K L` is the ring homomorphism $L \otimes_K K_\infty \to$ `InfiniteAdeleRing L` given by the commutativity isomorphism $L \otimes_K K_\infty \cong K_\infty \otimes_K L$ followed by the base-change comparison isomorphism attached to `genuineInfinitePlaceData`; likewise $\iota :=$ `ringEquiv_mixedSpace K` on $K_\infty$. For an infinite place $w'$ of $L$, `archEval L w'` is the evaluation ring homomorphism `InfiniteAdeleRing L` $\to L_{w'}$, and similarly over $K$. Finally, `sigmaTensor K L K_∞ σ` is the ring endomorphism $\sigma_E := \sigma \otimes \mathrm{id}$ of $E$, `diagUnits2 x y` is the element of $\mathrm{GL}_2$ with matrix $\mathrm{diag}(x,y)$, `toTensorGL K L K_∞` is the map $\mathrm{GL}_2(K_\infty) \to \mathrm{GL}_2(E)$ induced by $a \mapsto 1 \otimes a$, and `normString K L K_∞ σ δ` is the ordered product $\delta \cdot \sigma_E(\delta) \cdots \sigma_E^{\ell-1}(\delta)$, $\sigma_E$ acting entrywise on $\mathrm{GL}_2(E)$.
--
--   The kernel hypotheses are: $\Phi : (\mathrm{Fin}\,3 \to$ `mixedSpace L`$) \to \mathbb{C}$ is $C^\infty$ over $\mathbb{R}$ (`hΦ`), has compact support (`hΦc`), and satisfies the unit-support condition `hΦu`: there is a compact set $C \subseteq E^\times \times E^\times$ such that every $p$ in the closed support of $\Phi$ admits $q \in C$ with $p\,0 = \iota_L(q_1)$ and $p\,1 = \iota_L(q_2)$. Lastly $w$ is an infinite place of $K$, assumed complex (`hw`).
--
--   The assertion is the existence of two functions $A, B : (\mathrm{Fin}\,2 \to$ `mixedSpace K`$) \to \mathbb{C}$ with the following five properties. First, $A$ and $B$ are $C^\infty$ over $\mathbb{R}$. Second, both have compact support. Third, there is a compact set $C_a \subseteq K_\infty^\times \times K_\infty^\times$ such that every $p$ in the union of the closed supports of $A$ and of $B$ equals $![\,\iota(q_1), \iota(q_2)\,]$ for some $q \in C_a$. Fourth and fifth (one universally quantified clause), for all $a, t \in K_\infty^\times$ such that the component of $t$ at every infinite place $v$ of $K$ is $\neq 1$, and for all $\alpha, \beta \in E^\times$ with
--   $$\mathrm{normString}(\mathrm{diag}(\alpha,\beta)) = \mathrm{toTensorGL}\big(\mathrm{diag}(a, at)\big),$$
--   the following hold. Write, for $u = (u_1,u_2) \in U_1 \times U_1$, $\delta_1(u) = \alpha u_1$, $\delta_2(u) = \beta u_2$ and $r_u = (\alpha u_1)^{-1}(\beta u_2) \in E^\times$, viewed in $E$, and put for $y \in E$
--   $$\omega_w(y) = \sum_{\substack{w' \text{ infinite place of } L \\ w'|_K = w}} m_{w'}\,\log\big(1 + \|y_{w'}\|^2\big) \in \mathbb{R},$$
--   where $m_{w'} =$ `w'.mult`, $y_{w'} =$ `archEval L w' (archIdent K L y)`, and the sum is over the places of $L$ whose comap along $K \to L$ is $w$; $\omega_w(y)$ is coerced to $\mathbb{C}$.
--
--   (i) For every $u \in U_1 \times U_1$ the function $y \mapsto \Phi\,![\,\iota_L\delta_1(u),\ \iota_L\delta_2(u),\ \iota_L(\sigma_E y - r_u\, y)\,] \cdot \omega_w(y)$ is $\lambda$-integrable on $E$.
--
--   (ii) The function $u \mapsto \int_E \Phi\,![\,\iota_L\delta_1(u), \iota_L\delta_2(u), \iota_L(\sigma_E y - r_u y)\,]\,\omega_w(y)\,d\lambda(y)$ is integrable on $U_1 \times U_1$ for $\theta \times \theta$.
--
--   (iii) For every $u \in U_1 \times U_1$ the unweighted function $y \mapsto \Phi\,![\,\iota_L\delta_1(u), \iota_L\delta_2(u), \iota_L y\,]$ is $\lambda$-integrable.
--
--   (iv) The function $u \mapsto \int_E \Phi\,![\,\iota_L\delta_1(u), \iota_L\delta_2(u), \iota_L y\,]\,d\lambda(y)$ is $\theta \times \theta$-integrable.
--
--   (v) The identity
--   $$\Big(\prod_{v} \big\|(1-t)_v\big\|^{m_v}\Big) \int_{U_1\times U_1} \int_E \Phi\,![\,\iota_L\delta_1(u), \iota_L\delta_2(u), \iota_L(\sigma_E y - r_u y)\,]\,\omega_w(y)\,d\lambda\,d(\theta\times\theta)$$
--   $$= -2\,\ell\,\Big(m_w \log \big\|(1-t)_w\big\|\Big) \int_{U_1\times U_1}\int_E \Phi\,![\,\iota_L\delta_1(u), \iota_L\delta_2(u), \iota_L y\,]\,d\lambda\,d(\theta\times\theta)$$
--   $$\quad + A\,![\,\iota(t), \iota(a)\,] + \Big(\big\|(1-t)_w\big\|^2 \log\big\|(1-t)_w\big\|\Big)\, B\,![\,\iota(t), \iota(a)\,],$$
--   where the product is over all infinite places $v$ of $K$, $m_v =$ `v.mult`, and $(1-t)_v =$ `archEval K v (1 - t)` with $t$ viewed in $K_\infty$; the real scalars are coerced to $\mathbb{C}$ and $\ell = \operatorname{finrank}_K L$ is cast to $\mathbb{C}$.
--
--   Thus the twisted integral of the kernel against the logarithmic weight $\omega_w$ attached to the fibre of $w$, weighted by the Jacobian factor $\prod_v \|(1-t)_v\|^{m_v}$, is expressed as a multiple of the corresponding unweighted twisted integral by $-2\ell\, m_w \log\|(1-t)_w\|$, up to the two smooth compactly supported correction terms $A$ and $B$, the second carrying the factor $\|(1-t)_w\|^2 \log \|(1-t)_w\|$; the functions $A$ and $B$ do not depend on $a$, $t$, $\alpha$, $\beta$, being produced before these are quantified.
--
--   This is the archimedean twisted-weight comparison at a complex place of $K$: it isolates the logarithmic germ of the weighted twisted orbital integral over the norm-one fibre, in the shape $-2\ell\,m_w\log\|1-t_w\|$ times the unweighted integral plus smooth compactly supported remainders. It feeds the aggregation of such per-place layers into the global twisted weighted orbital identity used in the base-change comparison behind the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ)
    (hΦu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))))
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), (∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1) →
      ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
        (∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
            Integrable (fun y : (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
                    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ)) lam) ∧
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
            ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
                    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam) (θ.prod θ) ∧
        (∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker, Integrable (fun y : (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)]) lam) ∧
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam) (θ.prod θ) ∧
        ((∏ v : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K v ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ v.mult : ℝ) : ℂ) *
          ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
                    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam ∂(θ.prod θ) =
        -2 * (Module.finrank K L : ℂ) * (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam ∂(θ.prod θ) +
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by sorry
