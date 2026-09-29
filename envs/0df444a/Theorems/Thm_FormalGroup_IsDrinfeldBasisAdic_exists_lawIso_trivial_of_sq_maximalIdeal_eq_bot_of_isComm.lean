-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
-- name    : FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/469915a8-04d0-5a90-96ce-a7c1b2abd3d4
-- title:
--   Triviality of first-order lifts keeping (0,0) a Drinfeld basis
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $F_0$ a commutative formal group law over $k$ satisfying `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with the ideal $\bot$ supplying the adic data, its $q$-series $[q]_{F_0}$ equals a unit power series times the Drinfeld divisor $\mathrm{drinfeldDivisor}\,q\,0\,0$. Let $T$ be a commutative local $k$-algebra with $\mathfrak m_T^2 = \bot$, equipped with a ring homomorphism $\mathrm{resT} : T \to k$ that is a retraction of the structure map ($\mathrm{resT}(\mathrm{algebraMap}\,a) = a$ for all $a \in k$) and has kernel exactly $\mathfrak m_T$. Let $G$ be a commutative formal group law over $T$ which is a lift of $F_0$, in the sense that $F_0$'s two-variable series is the image of $G$'s under $\mathrm{MvPowerSeries.map\ resT}$, and which satisfies `IsDrinfeldBasisAdic (maximalIdeal T) q 0 0`, i.e. $[q]_G$ is a unit times the same Drinfeld divisor for the ideal $\mathfrak m_T$. Let $G_0$ be the constant lift, i.e. a formal group law over $T$ whose series is the image of $F_0$'s under $\mathrm{MvPowerSeries.map}$ of $\mathrm{algebraMap}\,k\,T$. Then there exists an isomorphism $\psi : G_0 \to G$ of formal group laws over $T$ — a power series with zero constant term and invertible linear coefficient satisfying $\psi(G_0(X_0,X_1)) = G(\psi(X_0),\psi(X_1))$ — whose coefficients reduce under $\mathrm{resT}$ to those of $X$: $\mathrm{resT}(\mathrm{coeff}_n \psi) = 1$ for $n = 1$ and $0$ otherwise.
--
--   This is the formal-group form of the statement that the Hasse invariant has simple zeros (Igusa; Katz–Mazur 12.4.4): for a height-two law, a first-order deformation on which the $q$-series still has the shape unit $\cdot\,X^{q^2}$ must be the trivial deformation, and moreover the isomorphism to the constant lift can be chosen congruent to $X$ modulo $\mathfrak m_T$. It feeds [`FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm`](thm.html#FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm) and [`FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot`](thm.html#FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra k T]
    (hsq : (maximalIdeal T) ^ 2 = ⊥)
    (resT : T →+* k) (hres : ∀ a : k, resT (algebraMap k T a) = a) (hker : RingHom.ker resT = maximalIdeal T)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (hD : G.IsDrinfeldBasisAdic (maximalIdeal T) q 0 0)
    (G₀ : FormalGroup T) (hG₀ : F₀.IsBaseChange (algebraMap k T) G₀) :
    ∃ ψ : FormalGroup.LawIso G₀ G, ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by sorry
