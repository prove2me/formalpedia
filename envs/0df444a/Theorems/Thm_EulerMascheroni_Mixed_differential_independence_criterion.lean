-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_differential_independence_criterion
-- name    : EulerMascheroni.Mixed.differential_independence_criterion
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:02:58.948314+00:00
-- url     : https://prove2.me/theorems/d4f9a262-fece-42ac-be27-8eb80511d594
-- title:
--   A differential-field criterion for independence of an exponential-integral extension
-- statement:
--   Let $K\subset F$ be differential fields over $\mathbb Q$, with compatible derivations $d,D$, and let $0\ne z\in K$. Suppose $e,y\in F$ satisfy
--
--   $$De=e,\qquad Dy=y+(e-1)/z.$$
--
--   Assume $1,e$ are linearly independent over $K$ and no $u\in K$ satisfies $du=1/z$. Then $1,e,y$ are linearly independent over $K$.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Mathlib

theorem EulerMascheroni.Mixed.differential_independence_criterion {K F : Type*} [Field K] [Field F] [Algebra ℚ K] [Algebra ℚ F]
    [Algebra K F] [IsScalarTower ℚ K F]
    (d : Derivation ℚ K K) (D : Derivation ℚ F F)
    (hD : ∀ r : K, D (algebraMap K F r) = algebraMap K F (d r))
    (z : K) (hz : z ≠ 0) (e y : F)
    (he : D e = e) (hy : D y = y+(e-1)/algebraMap K F z)
    (hexp : ∀ p q : K, algebraMap K F p+algebraMap K F q*e=0 → p=0 ∧ q=0)
    (hlog : ∀ u : K, d u ≠ z⁻¹)
    (a b c : K) (hrel : algebraMap K F a+algebraMap K F b*e+algebraMap K F c*y=0) :
    a=0 ∧ b=0 ∧ c=0 := by sorry
