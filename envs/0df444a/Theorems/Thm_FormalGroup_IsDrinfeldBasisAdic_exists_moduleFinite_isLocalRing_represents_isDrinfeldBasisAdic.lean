-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
-- name    : FormalGroup.IsDrinfeldBasisAdic.exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/0a18aa47-0cbd-5a73-b85b-39c1d9140402
-- title:
--   Representability of formal Drinfeld bases by a finite local algebra
-- statement:
--   Fix a prime $q$, a field $k$ of characteristic $q$, and a complete discrete valuation domain $W_0$ which is an integral domain, adically complete for its maximal ideal, with $\mathfrak m_{W_0}=(q)$, together with a surjective ring homomorphism $\mathrm{res}_0\colon W_0\to k$ whose kernel is $\mathfrak m_{W_0}$. Let $F_0$ be a commutative formal group over $k$ such that `F₀.IsDrinfeldBasisAdic ⊥ q 0 0` holds, i.e. taking the ideal $\bot$ as the ideal of definition there is a unit $u$ of $k\llbracket X\rrbracket$ with $F_0.\mathrm{nthSeries}\,q = u\cdot F_0.\mathrm{drinfeldDivisor}\,q\,0\,0$, and let $F_u$ be a commutative formal group over $W_0\llbracket t\rrbracket$ whose base change along $\mathrm{res}_0\circ\mathrm{constantCoeff}$ is $F_0$, meaning that the power series of $F_0$ is the coefficientwise image of that of $F_u$. The assertion is the existence of a commutative $W_0\llbracket t\rrbracket$-algebra $C$ which is local, module-finite over $W_0\llbracket t\rrbracket$ and adically complete for $\mathfrak m_C$, of a surjection $\mathrm{res}_C\colon C\to k$ with kernel $\mathfrak m_C$ satisfying $\mathrm{res}_C(f)=\mathrm{res}_0(\mathrm{constantCoeff}\,f)$ for all $f\in W_0\llbracket t\rrbracket$, of a formal group $G_c$ over $C$ that is the base change of $F_u$ along $W_0\llbracket t\rrbracket\to C$, and of elements $x_0,x_1\in\mathfrak m_C$ with $G_c.\mathrm{nthSeries}\,q$ a unit multiple of $G_c.\mathrm{drinfeldDivisor}\,q\,x_0\,x_1$ relative to $\mathfrak m_C$, which is universal: for every commutative local $W_0\llbracket t\rrbracket$-algebra $B$ adically complete for $\mathfrak m_B$, every formal group $G$ over $B$ obtained from $F_u$ by base change, and all $y_0,y_1\in\mathfrak m_B$ with `G.IsDrinfeldBasisAdic (maximalIdeal B) q y₀ y₁`, there is a unique $W_0\llbracket t\rrbracket$-algebra homomorphism $\chi\colon C\to B$ with $\chi(x_0)=y_0$ and $\chi(x_1)=y_1$.
--
--   This is the representability statement for the functor of Drinfeld bases of level $q$ on the Lubin–Tate type family $F_u$ over $W_0\llbracket t\rrbracket$: the pair of basis points is carried by a single finite local complete $W_0\llbracket t\rrbracket$-algebra with residue field $k$, universal among complete local $W_0\llbracket t\rrbracket$-algebras. It is used in the study of the Lubin–Tate coordinate on deformation rings with Drinfeld level structure, notably by [`FormalGroup.IsDrinfeldBasisAdic.injective_algHom_powerSeries_of_universal`](thm.html#FormalGroup.IsDrinfeldBasisAdic.injective_algHom_powerSeries_of_universal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra (PowerSeries W₀) C) (_ : IsLocalRing C)
      (_ : Module.Finite (PowerSeries W₀) C) (_ : IsAdicComplete (maximalIdeal C) C)
      (resC : C →+* k) (_ : Function.Surjective resC) (_ : RingHom.ker resC = maximalIdeal C)
      (_ : ∀ f : PowerSeries W₀, resC (algebraMap (PowerSeries W₀) C f) = res₀ (PowerSeries.constantCoeff f))
      (Gc : FormalGroup C) (_ : Fu.IsBaseChange (algebraMap (PowerSeries W₀) C) Gc)
      (x₀ x₁ : C) (_ : x₀ ∈ maximalIdeal C) (_ : x₁ ∈ maximalIdeal C)
      (_ : Gc.IsDrinfeldBasisAdic (maximalIdeal C) q x₀ x₁),
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra (PowerSeries W₀) B] [IsAdicComplete (maximalIdeal B) B]
        (G : FormalGroup B), Fu.IsBaseChange (algebraMap (PowerSeries W₀) B) G →
        ∀ (y₀ y₁ : B), y₀ ∈ maximalIdeal B → y₁ ∈ maximalIdeal B →
          G.IsDrinfeldBasisAdic (maximalIdeal B) q y₀ y₁ →
          ∃! χ : C →ₐ[PowerSeries W₀] B, χ x₀ = y₀ ∧ χ x₁ = y₁ := by sorry
