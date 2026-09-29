-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_polynomial_logarithmic_wronskian
-- name    : EulerMascheroni.Mixed.polynomial_logarithmic_wronskian
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:02:56.750801+00:00
-- url     : https://prove2.me/theorems/bc611a6c-7cd5-4fc9-96bf-1bec2ea68386
-- title:
--   Polynomial residue obstruction to a rational logarithmic primitive
-- statement:
--   For complex polynomials $p,q$,
--
--   $$X(pq'-p'q)=p^2\quad\Longrightarrow\quad p=0.$$
--
--   For nonzero $p$, the forbidden identity would say $(q/p)'=1/X$.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Mathlib
open Polynomial

theorem EulerMascheroni.Mixed.polynomial_logarithmic_wronskian (p q : ℂ[X])
    (h : X*(p*q.derivative-p.derivative*q)=p^2) : p=0 := by sorry
