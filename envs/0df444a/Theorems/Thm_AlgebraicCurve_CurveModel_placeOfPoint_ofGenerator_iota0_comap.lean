-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap
-- name    : AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iota0_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/4b56b7eb-d11d-5328-9d53-e2ee5e982f3a
-- title:
--   Places of t-chart models restrict along a field homomorphism
-- statement:
--   Let $K_0$ be a field of characteristic $0$, $L_0$ an extension of $K_0$ and $t_0 \in L_0$ a nonzero element with $L_0$ finite over both $K_0\langle t_0\rangle$ and $K_0\langle t_0^{-1}\rangle$; let $K, L, t$ satisfy the same hypotheses, and assume $t_0$ is transcendental over $K_0$ and $t$ over $K$. Write $\mathrm{chartRing}\,K\,(\{t\})$ for the subalgebra of elements of $L$ integral over $K[t] = \mathrm{Algebra.adjoin}\,K\,\{t\}$, and let `CurveModel.ofGenerator` $K\,t\,ht$ be the two-chart model built from $t$: a scheme `glued K t`, integral, proper and smooth of relative dimension $1$ over $\mathrm{Spec}\,K$, with function field identified with $L$ and with a bijection `placeOfPoint` from its closed points to the places of $L$ over $K$ (valuation subrings of $L$ containing $K$, distinct from $L$, with principal ideals). Given a ring homomorphism $\varphi \colon L_0 \to L$ and a ring homomorphism $\psi \colon \mathrm{chartRing}\,K_0\,(\{t_0\}) \to \mathrm{chartRing}\,K\,(\{t\})$ such that $\varphi$ agrees with $\psi$ on the chart ring, and given points $xb$ of the affine $t$-chart `X₀ K t` and $yb$ of `X₀ K₀ t₀` (each carrying a prime ideal `asIdeal` of the corresponding chart ring) whose images under the chart inclusions $\iota_0$ are closed points of the respective glued schemes, assume $yb.\mathrm{asIdeal} = \psi^{-1}(xb.\mathrm{asIdeal})$. Then the preimage under $\varphi$ of the valuation subring of $L$ attached by `placeOfPoint` to the image of $xb$ equals, as a subring of $L_0$, the valuation subring attached by `placeOfPoint` to the image of $yb$.
--
--   This is the place-compatibility clause for the affine $t$-chart: contraction of valuations along $\varphi$ matches contraction of primes along $\psi$, so that the place data of the constructed smooth proper model descends along a change of the base field. It is used in the identification of the modular-curve models over $\mathbb{Q}$ and over $\overline{\mathbb{Q}}$, in [`ModularCurve.IgusaScheme.ratPlaceCompat_of_chartPins`](thm.html#ModularCurve.IgusaScheme.ratPlaceCompat_of_chartPins) and [`ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat`](thm.html#ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat); a companion statement handles the chart at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IntermediateField IsDedekindDomain AlgebraicCurve AlgebraicCurve.CurveModel

theorem AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iota0_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀} : Set L₀) →+* chartRing K ({t} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀} : Set L₀), φ (a : L₀) = (ψ a : L))
    (xb : X₀ K t) (hxb : (ι₀ K t).base xb ∈ closedPoints (CurveModel.ofGenerator K t ht).C)
    (yb : X₀ K₀ t₀) (hyb : (ι₀ K₀ t₀).base yb ∈ closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint ⟨(ι₀ K t).base xb, hxb⟩).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint ⟨(ι₀ K₀ t₀).base yb, hyb⟩).toValuationSubring.toSubring := by sorry
