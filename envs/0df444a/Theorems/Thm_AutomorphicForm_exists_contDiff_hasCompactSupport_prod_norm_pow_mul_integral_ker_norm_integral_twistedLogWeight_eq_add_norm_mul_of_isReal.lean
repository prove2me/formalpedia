-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/5d3ff6c2-774d-56c2-bf7f-785b6b3c526a
-- title:
--   Twisted log-weight layer above a real place of K
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite Galois, and $\sigma \in \mathrm{Gal}(L/K)$ is an automorphism subject to two hypotheses: `hgen`, that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so $\sigma$ generates the Galois group), and `hdeg`, that $\ell := [L:K]$ is prime. Write $K_\infty$ for `InfiniteAdeleRing K` and $E := L \otimes_K K_\infty$. On $E$ a measurable space structure with the Borel property is fixed together with an additive Haar measure $\lambda$ (`lam`); on the unit group $E^\times$ a measurable space structure with the Borel property is fixed, and $\theta$ is a Haar measure on the subgroup $U_1 := \ker\big(E^\times \to K_\infty^\times\big)$, the kernel of the map induced on units by the algebra norm $\mathrm{N}_{E/K_\infty}$.
--
--   For $z \in E$ denote by $\iota_L(z)$ the element of `mixedSpace L` obtained as the image of $z$ under [`AutomorphicForm.archIdent K L`](def/AutomorphicForm_TwistedOrbital.html#L420) (the ring homomorphism $L \otimes_K K_\infty \to L_\infty$ given by the commutativity isomorphism followed by the base-change identification of infinite adele rings) followed by `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L`; similarly, for $x \in K_\infty$ let $\iota_K(x)$ be the element of `mixedSpace K` obtained as the image of $x$ under `ringEquiv_mixedSpace K`. Also write $\sigma_E$ for [`AutomorphicForm.sigmaTensor K L K_∞ σ`](def/AutomorphicForm_TwistedOrbital.html#L199), the ring endomorphism $\sigma \otimes \mathrm{id}$ of $E$.
--
--   The kernel datum is a function $\Phi$ from $\mathrm{Fin}\,3 \to$ `mixedSpace L` to $\mathbb{C}$ subject to three hypotheses: `hΦ`, that $\Phi$ is $C^\infty$ as a function of real variables; `hΦc`, that $\Phi$ has compact support; and `hΦu`, a uniformity hypothesis asserting the existence of a compact set $C \subseteq E^\times \times E^\times$ such that every $p$ in the closed support of $\Phi$ satisfies $p\,0 = \iota_L(q_1)$ and $p\,1 = \iota_L(q_2)$ for some $(q_1,q_2) \in C$ (the first two arguments of $\Phi$ are thus carried over a compact set of pairs of units of $E$). Finally $w$ is an infinite place of $K$, assumed real (`hw`).
--
--   For $y \in E$ put
--   $$\omega_w(y) \;=\; \sum_{\substack{w' \in \mathrm{InfinitePlace}\, L \\ w'|_K = w}} m_{w'} \, \log\!\big(1 + \|\,\iota_L(y)\ \text{at}\ w'\,\|^2\big) \in \mathbb{R},$$
--   the sum being over the places $w'$ of $L$ whose restriction along the algebra map $K \to L$ is $w$, with $m_{w'}$ the multiplicity `w'.mult`, and the norm being that of the component `archEval L w' (archIdent K L y)` in the completion at $w'$; $\omega_w(y)$ enters the integrals below through its complex cast.
--
--   The conclusion asserts the existence of two functions $A, B$ from $\mathrm{Fin}\,2 \to$ `mixedSpace K` to $\mathbb{C}$ which are $C^\infty$ over $\mathbb{R}$, have compact support, and satisfy the same kind of uniformity as $\Phi$: there is a compact set $C_a \subseteq K_\infty^\times \times K_\infty^\times$ such that every $p$ in the union of the closed supports of $A$ and $B$ is of the form $p = \,![\iota_K(q_1), \iota_K(q_2)]$ for some $(q_1,q_2) \in C_a$; and such that the following holds.
--
--   Let $a, t \in K_\infty^\times$ with $t$ subject to the condition that its component at every infinite place $v$ of $K$ is $\neq 1$, and let $\alpha, \beta \in E^\times$ satisfy the norm-string condition
--   $$\prod_{i=0}^{\ell-1} \big(\sigma_E\text{-twist}\big)^{i}\!\big(\mathrm{diag}(\alpha,\beta)\big) \;=\; \mathrm{diag}(a, at)\ \text{in}\ \mathrm{GL}_2(E),$$
--   that is, [`AutomorphicForm.normString K L K_∞ σ (diagUnits2 α β)`](def/AutomorphicForm_TwistedOrbital.html#L205) — the ordered product over $i \in \{0,\dots,\ell-1\}$ of the $i$-th iterate of the entrywise map induced by $\sigma_E$ applied to the diagonal matrix with entries $\alpha,\beta$ — equals the image of $\mathrm{diag}(a, at)$ under [`AutomorphicForm.toTensorGL K L K_∞`](def/AutomorphicForm_TwistedOrbital.html#L71) (entrywise base change along $K_\infty \to E$). For $u = (u_1,u_2) \in U_1 \times U_1$ write $\delta_u = (\alpha u_1, \beta u_2) \in E^\times \times E^\times$ and $r_u = (\alpha u_1)^{-1}(\beta u_2) \in E^\times$. Then five assertions hold.
--
--   First, for every $u \in U_1 \times U_1$ the function
--   $$y \longmapsto \Phi\big[\iota_L(\alpha u_1),\ \iota_L(\beta u_2),\ \iota_L(\sigma_E y - r_u\, y)\big] \cdot \omega_w(y)$$
--   is $\lambda$-integrable on $E$.
--
--   Secondly, the function sending $u \in U_1 \times U_1$ to $\int_E$ of the above integrand with respect to $\lambda$ is integrable for the product measure $\theta \otimes \theta$.
--
--   Thirdly, for every $u \in U_1 \times U_1$ the unweighted function $y \mapsto \Phi\big[\iota_L(\alpha u_1), \iota_L(\beta u_2), \iota_L(y)\big]$ is $\lambda$-integrable.
--
--   Fourthly, the function sending $u$ to $\int_E \Phi\big[\iota_L(\alpha u_1), \iota_L(\beta u_2), \iota_L(y)\big]\, d\lambda(y)$ is $\theta \otimes \theta$-integrable.
--
--   Fifthly, the identity
--   $$\Big(\prod_{v} \big\|\,\text{component of } 1-t \text{ at } v\,\big\|^{m_v}\Big) \int_{U_1^2}\!\!\int_E \Phi\big[\iota_L(\alpha u_1), \iota_L(\beta u_2), \iota_L(\sigma_E y - r_u y)\big]\,\omega_w(y)\, d\lambda\, d(\theta\otimes\theta)$$
--   $$= -2\,\ell\; \big(m_w \log\|\,\text{component of } 1-t \text{ at } w\,\|\big) \int_{U_1^2}\!\!\int_E \Phi\big[\iota_L(\alpha u_1), \iota_L(\beta u_2), \iota_L(y)\big]\, d\lambda\, d(\theta\otimes\theta)$$
--   $$\qquad + A\big[\iota_K(t), \iota_K(a)\big] \;+\; \big\|\,\text{component of } 1-t \text{ at } w\,\big\| \cdot B\big[\iota_K(t), \iota_K(a)\big]$$
--   holds, where the product is over all infinite places $v$ of $K$ with $m_v$ the multiplicity `v.mult`, the components of $1 - t$ are taken via `archEval K v` and `archEval K w`, $\ell = [L:K]$ is `Module.finrank K L` cast to $\mathbb{C}$, and all real quantities are cast to $\mathbb{C}$. Note that the arguments of $A$ and $B$ are the pair $(\iota_K(t), \iota_K(a))$ in this order.
--
--   This is the archimedean weight layer, attached to a single real place $w$ of $K$, of the twisted orbital integrals occurring in the comparison of trace formulae for cyclic base change of $\mathrm{GL}_2$: it expresses the $\omega_w$-weighted twisted integral, normalised by the Jacobian factor $\prod_v \|1-t_v\|^{m_v}$, as $-2\ell\, m_w \log\|1-t_w\|$ times the unweighted twisted integral plus smooth compactly supported error terms $A$ and $B$, the second damped by $\|1-t_w\|$. It is obtained from the per-place-of-$L$ statements above $w$ (real and complex cases) together with the construction of the $K_\infty$-linear resolvent of $\sigma_E - r_u$, and is used in the assembly of the twisted weighted orbital integral over all infinite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal.lean

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

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal
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
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
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
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by sorry
