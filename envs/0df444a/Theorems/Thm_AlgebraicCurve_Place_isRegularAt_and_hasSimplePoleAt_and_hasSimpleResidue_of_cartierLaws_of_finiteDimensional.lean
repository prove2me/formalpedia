-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
-- name    : AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/17ca36ff-d6b7-5bc0-81f2-76989cf71e99
-- title:
--   Cartier operator: regularity, simple poles, p-th roots of residues
-- statement:
--   Let $K$ be a perfect field and $F$ a field with a $K$-algebra structure such that [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15) holds, i.e. every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place is $\mathrm{ord}_v(f)$, each residue field of a place is a finite $K$-module, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Let $p$ be a prime with $K$ of characteristic $p$, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $C : \Omega_{F/K} \to \Omega_{F/K}$ be additive and satisfy Cartier's three laws: $C(f^p \cdot \omega) = f \cdot C\omega$, $C(\mathrm{d}f) = 0$ and $C(f^{p-1}\cdot \mathrm{d}f) = \mathrm{d}f$ for all $f \in F$. Fix a place $v$ of $F/K$ — a valuation subring $\mathcal{O}_v \subsetneq F$ containing $\mathrm{image}(K)$ and a principal ideal ring — with its chosen uniformiser $\pi$ and coordinate differential $\mathrm{d}\pi$, and fix $\omega \in \Omega_{F/K}$. The conclusion is a conjunction of three implications. First, if $\omega = f\cdot \mathrm{d}\pi$ for some $f \in \mathcal{O}_v$, then $C\omega = g \cdot \mathrm{d}\pi$ for some $g \in \mathcal{O}_v$. Second, if $\omega = f \cdot \mathrm{d}\pi$ with $\pi f \in \mathcal{O}_v$, then $C\omega = g\cdot\mathrm{d}\pi$ with $\pi g \in \mathcal{O}_v$. Third, for every $r \in K$, if $\omega = f\cdot \mathrm{d}\pi$ with $\pi f \in \mathcal{O}_v$ having residue the image of $r$ in the residue field of $v$, then there is $s \in K$ with $s^p = r$ and $C\omega = g \cdot \mathrm{d}\pi$ for some $g$ with $\pi g \in \mathcal{O}_v$ of residue the image of $s$.
--
--   This is the local theory of Cartier's operator on differentials of a function field in characteristic $p$: it is regular, respectively has at most a simple pole, at a place whenever the differential does, and it extracts the $p$-th root of a simple residue. It is used in the construction of Cartier-fixed regular differentials over an algebraically closed constant field and in the computation of residues of $q$-expansion differentials at Frobenius-image places of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
    {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hC1 : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hC2 : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hC3 : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    (v.IsRegularAt ω → v.IsRegularAt (C ω)) ∧
      (v.HasSimplePoleAt ω → v.HasSimplePoleAt (C ω)) ∧
      (∀ r : K, v.HasSimpleResidue ω r → ∃ s : K, s ^ p = r ∧ v.HasSimpleResidue (C ω) s) := by sorry
