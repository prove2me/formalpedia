-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing
-- name    : FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/ff489155-9e49-5a44-90dc-c191c0f7ade0
-- title:
--   Drinfeld basis gives a W[[X₀,X₁]]/(varpi v-fu) presentation
-- statement:
--   Fix a prime $q\ge 3$. Let $R$ be a Noetherian local ring, complete for the $\mathfrak m$-adic topology ($\mathfrak m=$ `maximalIdeal R`), regular, with `ringKrullDim R = 2`, whose residue field is finite of characteristic $q$. Let $F$ be a commutative formal group law over $R$, and let $x_0,x_1\in R$ satisfy $\mathfrak m=(x_0,x_1)$ and the hypothesis `F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁`, i.e. with $R$ equipped with the ideal $\mathfrak m$ there is a unit power series $u$ over $R$ with `F.nthSeries q = u * F.drinfeldDivisor q x₀ x₁`. Let further $A$ be a discrete valuation domain with $\mathrm{maximalIdeal}\,A=(\varpi)$, let $\varepsilon\in A$ be a unit with $\varpi^{q-1}=\varepsilon q$, and let $\iota:A\to R$ be a local ring homomorphism. The conclusion asserts the existence of a discrete valuation domain $W$, complete for its maximal-adic topology, a ring homomorphism $\sigma:A\to W$ with $\mathrm{maximalIdeal}\,W=(\sigma\varpi)$, and power series $f,u,v\in W[[X_0,X_1]]$ with $u,v$ units and $f-(X_0X_1^{\,q}-X_0^{\,q}X_1)\in (X_0,X_1)^{q+2}$, together with a ring isomorphism $e:R\xrightarrow{\ \sim\ } W[[X_0,X_1]]/(C(\sigma\varpi)\,v-f\,u)$ such that $e(\iota a)$ is the class of the constant $C(\sigma a)$ for every $a\in A$, and $e(x_0)$, $e(x_1)$ are the classes of $X_0$, $X_1$.
--
--   This is the local structure theorem for a regular two-dimensional complete local ring carrying a formal group law with an $\mathfrak m$-adic Drinfeld basis of level $q$: such a ring is a hypersurface $W[[X_0,X_1]]/(\varpi v-fu)$ whose equation agrees with the Drinfeld form $X_0X_1^{\,q}-X_0^{\,q}X_1$ to order $q+2$. It is used to obtain reducedness of the corresponding quotient and, in the analysis of modular curves of full level structure, to identify adic completions of stalks at supersingular points on the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (hchar : CharP (ResidueField R) q) [Finite (ResidueField R)]
    (F : FormalGroup R) [F.IsComm]
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W)
      (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}),
      (∀ a : A, e (ι a) = Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by sorry
