-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_polynomial_exponential_wronskian
-- name    : EulerMascheroni.Mixed.polynomial_exponential_wronskian
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:02:29.598974+00:00
-- url     : https://prove2.me/theorems/b2b8f527-859c-4c26-bd1b-2b4dc326f2eb
-- title:
--   Polynomial degree obstruction to a rational exponential solution
-- statement:
--   For complex polynomials $p,q$,
--
--   $$p'q-pq'=pq\quad\Longrightarrow\quad p=0\ \text{or}\ q=0.$$
--
--   This is the polynomial obstruction to a nonzero rational function satisfying $u'=u$.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Mathlib
open Polynomial

theorem EulerMascheroni.Mixed.polynomial_exponential_wronskian (p q : ℂ[X])
    (h : p.derivative*q-p*q.derivative=p*q) : p=0 ∨ q=0 := by sorry
