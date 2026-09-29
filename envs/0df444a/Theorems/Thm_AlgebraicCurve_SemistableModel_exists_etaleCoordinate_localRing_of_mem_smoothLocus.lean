-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus
-- name    : AlgebraicCurve.SemistableModel.exists_etaleCoordinate_localRing_of_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/6d81e032-27d3-56b5-acd2-6eec4d8ae121
-- title:
--   Étale coordinate at a smooth closed point of the special fibre
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, and let $F$ be a field with an $L$-algebra structure which is a curve over $L$ in the project's sense (every nonzero element of $F$ has a divisor of degree $0$ recording its orders at all places, every place of $F/L$ has residue field finite over $L$, and $\Omega[F \mathbin{/} L]$ is free of rank one over $F$). Let $X$ be an integral scheme with a morphism `toBase` to $\operatorname{Spec} A$ that is locally of finite presentation, and let $\varphi \colon F \to X$'s function field be a ring isomorphism carrying $\operatorname{algebraMap} L F (a)$, for $a \in A$, to the image of $a$ under the canonical map $A \to \mathcal O_{X,\xi}$, $\xi$ the generic point, composed into the function field. Let $x \in X$ lie over the closed point of $A$, be closed (any $y$ with $x \rightsquigarrow y$ equals $x$), and lie in the smooth locus of `toBase`; let $\eta \neq x$ be a further point over the closed point of $A$ with $\eta \rightsquigarrow x$. Put $S :=$ `SemistableModel.localRing X φ x`, the subring of $F$ obtained by transporting the image of $\mathcal O_{X,x}$ in the function field through $\varphi^{-1}$. Then there exist a ring homomorphism $\iota \colon A \to S$ with $\iota(a) = a$ in $F$ for all $a \in A$, an element $t \in S$, and a ring homomorphism $\chi_0 \colon S \to$ the residue field of $A$, such that: $S$ is local; the units of $S$ are exactly the $f$ with $\chi_0 f \neq 0$; $\chi_0 \circ \iota$ is the residue map of $A$; $\chi_0 t = 0$; the homomorphism $A[T] \to S$ given by $\iota$ on coefficients and $T \mapsto t$ is formally smooth and formally unramified; every $f$ with $\chi_0 f = 0$ can be written $f = g t + s$ with $g \in S$ and $s$ in the ideal $\mathfrak m_A S := (\operatorname{maximalIdeal} A).\mathrm{map}\ \iota$ (the inclusion $\mathfrak m_S \subseteq (t) + \mathfrak m_A S$ only); $\mathfrak m_A S$ is prime and does not contain $t$; $S / \mathfrak m_A S$ is noetherian; an element $f \in F$ lies in `SemistableModel.localRing X φ η` if and only if $f h = g$ for some $g, h \in S$ with $h \notin \mathfrak m_A S$; every $f \in F$ satisfies $f h = g$ for some $g, h \in S$ with $h \neq 0$; and there are a commutative ring $P$ with an $A$-algebra structure of finite presentation, a submonoid $M \subseteq P$ and a $P$-algebra structure on $S$ exhibiting $S$ as the localisation of $P$ at $M$, with $A \to P \to S$ equal to $\iota$.
--
--   This records the classical structure of the stalk at a smooth closed point of the special fibre of a relative curve over a valuation ring: a lifted uniformiser of the smooth fibre curve serves as an étale coordinate, the fibre ideal $\mathfrak m_A S$ is prime with noetherian quotient, and the local ring at the generic point $\eta$ of the component through $x$ is the localisation of $S$ at $\mathfrak m_A S$. It feeds [`AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper`](thm.html#AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper), which packages this data for the smooth points of a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.exists_etaleCoordinate_localRing_of_mem_smoothLocus
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∃ (ι : ↥A →+* ↥S) (_ : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
      (t : ↥S) (χ₀ : ↥S →+* ResidueField ↥A),
      IsLocalRing ↥S ∧
      (∀ f : ↥S, IsUnit f ↔ χ₀ f ≠ 0) ∧
      (∀ a : ↥A, χ₀ (ι a) = IsLocalRing.residue ↥A a) ∧
      χ₀ t = 0 ∧
      (Polynomial.eval₂RingHom ι t).FormallySmooth ∧ (Polynomial.eval₂RingHom ι t).FormallyUnramified ∧
      (∀ f : ↥S, χ₀ f = 0 → ∃ g : ↥S, ∃ s ∈ (maximalIdeal ↥A).map ι, f = g * t + s) ∧
      ((maximalIdeal ↥A).map ι).IsPrime ∧ t ∉ (maximalIdeal ↥A).map ι ∧
      IsNoetherianRing (↥S ⧸ (maximalIdeal ↥A).map ι) ∧
      (∀ f : F, f ∈ SemistableModel.localRing X φ η ↔
        ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∃ (P : Type) (_ : CommRing P) (_ : Algebra ↥A P) (_ : Algebra.FinitePresentation ↥A P)
          (M : Submonoid P) (_ : Algebra P ↥S) (_ : IsLocalization M ↥S),
        ∀ a : ↥A, algebraMap P ↥S (algebraMap ↥A P a) = ι a) := by sorry
