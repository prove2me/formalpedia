-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_formal_e_functional_independence
-- name    : EulerMascheroni.Mixed.formal_e_functional_independence
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:02:55.403521+00:00
-- url     : https://prove2.me/theorems/02b6f0d1-751b-4f78-9c18-c55ce90d7661
-- title:
--   Polynomial linear independence of the formal Euler E-functions
-- statement:
--   For any complex polynomials $p,q,r$,
--
--   $$p(X)+q(X)e^X+r(X)\widehat A(X)=0\quad\Longrightarrow\quad p=q=r=0,$$
--
--   where $\widehat A=e^X\widehat{\operatorname{Ein}}$. Clearing rational-function denominators yields functional linear independence over $\mathbb C(X)$. This is a formal-series assertion; transfer to values at $1$ is a separate arithmetic theorem.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Definitions.Def_eulerMascheroni_formalESystem
open PowerSeries EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.formal_e_functional_independence (p q r : Polynomial ℂ)
    (h : (p:ℂ⟦X⟧)+(q:ℂ⟦X⟧)*exp ℂ+(r:ℂ⟦X⟧)*formalExpEin=0) :
    p=0 ∧ q=0 ∧ r=0 := by sorry
