-- Prove2me | Theorems.Thm_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem
-- name    : FormalGroup.exists_ringHom_mvPowerSeries_eval_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/5b7b1d6f-a618-50da-8f0f-8854440fab0f
-- title:
--   Adic evaluation of two-variable power series at ideal elements
-- statement:
--   Let $A$ and $T$ be commutative rings in a common universe, let $f : A \to T$ be a ring homomorphism, and let $I \subseteq T$ be an ideal with respect to which $T$ is adically complete. Let $\zeta_0,\zeta_1 \in I$. Then there is a ring homomorphism $e : A[[X_0,X_1]] \to T$ (formal power series in the two variables indexed by `Fin 2`) with the following five properties. First, $e(\mathrm{C}(a)) = f(a)$ for every $a \in A$; second, $e(X_0) = \zeta_0$ and $e(X_1) = \zeta_1$. Third, for every formal group law $F$ over $A$ and every formal group law $G$ over $T$ such that the underlying series of $G$ is the image of that of $F$ under the coefficientwise map induced by $f$ (the predicate `IsBaseChange`), the evaluation of $G$ at the pair $(\zeta_0,\zeta_1)$ in the $I$-adic topology on $T$ — that is, `MvPowerSeries.eval₂` of $G$'s series along the identity of $T$ at $![\zeta_0,\zeta_1]$ — equals $e$ applied to the series of $F$. Fourth, for every one-variable power series $p$ over $A$ and every $i \in \{0,1\}$, $e$ of the substitution of $X_i$ into $p$ equals the $I$-adic evaluation of the coefficientwise image `PowerSeries.map f p` at $\zeta_0$ if $i = 0$ and at $\zeta_1$ otherwise. Fifth, if $F \in A[[X_0,X_1]]$ has all coefficients of total degree $< n$ equal to zero, then $e(F) \in I^n$.
--
--   This is the $I$-adic evaluation homomorphism attached to a pair of elements of $I$ in an $I$-adically complete ring: it specialises two-variable formal power series over $A$ to $T$ compatibly with base change of formal group laws along $f$, with one-variable substitutions, and with the $I$-adic filtration. It is used in the construction of points and parametrisations attached to a formal group, being cited by [`WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open FormalGroup

theorem FormalGroup.exists_ringHom_mvPowerSeries_eval_of_mem
    {A T : Type u} [CommRing A] [CommRing T] (f : A →+* T) (I : Ideal T) [IsAdicComplete I T]
    (ζ₀ ζ₁ : T) (h₀ : ζ₀ ∈ I) (h₁ : ζ₁ ∈ I) :
    ∃ e : MvPowerSeries (Fin 2) A →+* T,
      (∀ a : A, e (MvPowerSeries.C a) = f a) ∧ e (MvPowerSeries.X 0) = ζ₀ ∧ e (MvPowerSeries.X 1) = ζ₁ ∧
      (∀ (F : FormalGroup A) (G : FormalGroup T), F.IsBaseChange f G →
        (letI : WithIdeal T := ⟨I⟩; G.eval ζ₀ ζ₁) = e F.toPowerSeries) ∧
      (∀ (p : PowerSeries A) (i : Fin 2),
        e (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) p) =
          (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries (PowerSeries.map f p) (if i = 0 then ζ₀ else ζ₁))) ∧
      (∀ (n : ℕ) (F : MvPowerSeries (Fin 2) A), (∀ d : Fin 2 →₀ ℕ, d 0 + d 1 < n → MvPowerSeries.coeff d F = 0) →
        e F ∈ I ^ n) := by sorry
