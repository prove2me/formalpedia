-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_algebraic_quotient_boundary
-- name    : EulerMascheroni.Mixed.algebraic_quotient_boundary
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:38:07.38681+00:00
-- url     : https://prove2.me/theorems/5b56bab8-31ab-4786-bea0-c93859899c46
-- title:
--   Algebraicity of the boundary forced by a decaying mixed quotient
-- statement:
--   Let complex sequences $f_n,b_n$ and constants $c,s\in\mathbb C$ satisfy
--
--   $$b_0=c-f_0,\qquad b_{n+1}=b_n-f_{n+1},\qquad\sum_{n\ge0}f_n=s,\qquad b_n\longrightarrow0.$$
--
--   If $f_0$ and $b_0$ are algebraic, then
--
--   $$s\in\overline{\mathbb Q}.$$
--
--   This isolates the elementary boundary argument in arithmetic mixed division. The existence of such a quotient with algebraic coefficients is an additional hypothesis, not a conclusion of this theorem.
-- source:
--   Elementary summation and algebraic-closure argument derived for the mixed quotient decomposition; compare Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Proposition 2 and its proof in §3.1, pp. 6–7. The present theorem states all convergence and coefficient hypotheses explicitly and does not assume or prove arithmetic division.

import Mathlib

theorem EulerMascheroni.Mixed.algebraic_quotient_boundary (f b : ℕ → ℂ) (c s : ℂ)
    (hb0 : b 0 = c - f 0)
    (hrec : ∀ n, b (n+1) = b n - f (n+1))
    (hsum : HasSum f s)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (hf0 : IsAlgebraic ℚ (f 0)) (hba : IsAlgebraic ℚ (b 0)) :
    IsAlgebraic ℚ s := by sorry
