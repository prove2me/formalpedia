-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/0f053c3f-e696-5361-a96a-0acf8b7215d1
-- title:
--   Germ of [n] is n in End(X₀.F)
-- statement:
--   Fix a prime $r$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$ and a commutative ring $k_0$. Let $A_0$ be a fake elliptic curve over $k_0$ in the sense of the project structure (a scheme with a structure morphism to $\operatorname{Spec} k_0$, a commutative relative group law $L$, an abelian-scheme property bundle, two-dimensional fibres, and an action of $\Lambda$ by endomorphisms over the base that is additive and multiplicative in the prescribed sense and has the trace property), let $\mathrm{coord} : \Lambda \to \mathbb{W}(\mathbb F_{r^2})^2$ satisfy `IsOrderCoord` (additive, $1 \mapsto (1,0)$, multiplicative for the Frobenius-twisted product, injective, dense, trace-compatible), let $X_0$ be a formal $\mathcal O_D$-module over $k_0$ (a commutative formal group law $X_0.F$ in two variables with a $\mathbb{W}(\mathbb F_{r^2})$-action and a uniformiser series $\varpi$), and let $\theta_0$ be a system of formal coordinates in two variables for $A_0.f$ with $A_0.\mathrm{IsFormalModuleVia}\ \mathrm{coord}\ X_0\ \theta_0$, i.e. $\theta_0$ is a system of formal coordinates for $L$ with formal group $X_0.F$ and, on every nilpotent parameter, $\theta_0$ transports the series $\mathrm{addVia}\,X_0.F\,(X_0.\mathrm{act}\,(\mathrm{coord}\,m)_1)\,((X_0.\mathrm{act}\,(\mathrm{coord}\,m)_2)\circ\varpi)$ to post-composition with $A_0.\mathrm{act}\,m$. Assume $1 \in \Lambda$, let $n$ be a natural number with $n \in \Lambda$, let $B'$ be a commutative $k_0$-algebra, $J \subseteq B'$ an ideal with $J^{m+1} = 0$, and $s : \mathrm{Fin}\,2 \to B'$ with all $s_i \in J$. Then $\theta_0$ evaluated at the componentwise truncated evaluation (`nilEval` in degree $m$) at $s$ of the power-series tuple of $n$ regarded as an element of $\operatorname{End}(X_0.F)$ equals the result of post-composing $\theta_0\,B'\,s$ with the endomorphism $A_0.\mathrm{act}\,\langle n, hn\rangle$.
--
--   This identifies the formal germ of the endomorphism of a fake elliptic curve given by the integer $n \in \Lambda$ with the integer $n$ in the endomorphism ring of the associated two-dimensional formal group law, the scalar case of the compatibility encoded by `IsFormalModuleVia`. It is used in the rigidification arguments for fake elliptic curves, where germs of isogenies and of their duals must be recognised as central integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k₀ : Type} [CommRing k₀]
    (A₀ : FakeEllipticCurve Λ N k₀) (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (X₀ : FormalODModule r k₀) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ) (hJ : J ^ (m + 1) = ⊥)
    (s : Fin 2 → B') (hs : ∀ i, s i ∈ J) :
    θ₀ B' (fun i => MvFormalGroup.nilEval m (((n : MvFormalGroup.End X₀.F)).toPowerSeries i) s) =
      mapPt (A₀.act ⟨((n : ℕ) : ℚ), hn⟩) (A₀.act_over _) (θ₀ B' s) := by sorry
