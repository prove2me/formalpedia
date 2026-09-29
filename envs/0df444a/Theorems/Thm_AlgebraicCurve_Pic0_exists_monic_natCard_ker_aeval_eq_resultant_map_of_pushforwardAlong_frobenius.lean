-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius
-- name    : AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/1c794764-9610-50f6-90a8-5da0ad871d09
-- title:
--   Frobenius degree theory on Pic⁰: #ker G(T)=Res(G,P)
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and let $F_0$ be a field extension of $k$ and $F$ a field extension of both $K$ and $F_0$, all compatibly, such that $F_0/k$ and $F/K$ each satisfy `IsCurveOver`: principal divisors exist (every nonzero element has a degree-zero divisor recording its orders at all places), every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one. Assume $F_0$ is generated over $k$ by a finite set of elements, and that $K$ together with the image of $F_0$ generates $F$. Let $\varphi : F \to F$ be a $K$-algebra endomorphism whose underlying ring homomorphism is integral and which acts on the image of $F_0$ by $x \mapsto x^{\#k}$. Let $T$ be an endomorphism of the additive group $\mathrm{Pic}^0(F/K)$ — the quotient of the group of degree-zero divisors, i.e. finitely supported $\mathbb{Z}$-valued functions on the places of $F/K$ weighted by residue degrees, by the principal ones — which on the class of each degree-zero divisor $D$ is the class of the pushforward of $D$ along $\varphi$ (places restricted along $\varphi$, with multiplicities scaled by inertia degrees). Then there is a monic $P \in \mathbb{Q}[X]$ with $\deg P = 2\,g$, where $g = \operatorname{genusFF} K F$ is the $K$-dimension of $H^1$ of the zero divisor, such that for every monic $G \in \mathbb{Z}[X]$ whose constant coefficient has nonzero image in $K$, the kernel of the endomorphism $G(T)$ of $\mathrm{Pic}^0(F/K)$ is finite and its cardinality, viewed in $\mathbb{Q}$, equals the resultant of the image of $G$ in $\mathbb{Q}[X]$ with $P$.
--
--   This is the degree theory of the Frobenius endomorphism on the Jacobian of a curve over a finite field, read on the subring $\mathbb{Z}[\pi]$ and expressed through a single monic rational polynomial of degree $2g$ whose resultants against monic integral polynomials compute kernel orders exactly. It feeds the counting of Frobenius fixed points on $\mathrm{Pic}^0$ and the polynomial-interpolation form of these orders, which are used in the point-counting input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * AlgebraicCurve.genusFF K F ∧
      ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ∧
        ((Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker : ℕ) : ℚ) =
          (G.map (Int.castRingHom ℚ)).resultant P := by sorry
