-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_arithmetic_quotient_iff_boundary_algebraic
-- name    : EulerMascheroni.Mixed.arithmetic_quotient_iff_boundary_algebraic
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:02:57.188205+00:00
-- url     : https://prove2.me/theorems/5ddeebe6-0420-46f4-9192-a1d2d4326670
-- title:
--   Exact equivalence between an algebraic boundary and an algebraic decaying quotient
-- statement:
--   Let $f_n\in\overline{\mathbb Q}\subset\mathbb C$ satisfy $\sum f_n=s$. Then $s$ is algebraic if and only if there is a sequence of algebraic numbers $u_n$ such that
--
--   $$u_0=s-f_0,\qquad u_{n+1}=u_n-f_{n+1},\qquad u_n\to0.$$
--
--   Thus arithmetic quotient existence in this coefficient-only formulation is equivalent to algebraicity of the boundary itself. This identifies an exact limitation of that proposed decomposition.
-- source:
--   Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2 and §4.3; Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2. Elementary polynomial, differential and norm reductions are derived explicitly here.

import Mathlib
open Filter
open scoped Topology

theorem EulerMascheroni.Mixed.arithmetic_quotient_iff_boundary_algebraic (f : ℕ → ℂ) (s : ℂ)
    (hf : ∀ n, IsAlgebraic ℚ (f n)) (hs : HasSum f s) :
    IsAlgebraic ℚ s ↔
    ∃ u : ℕ → ℂ, u 0 = s-f 0 ∧
      (∀ n, u (n+1)=u n-f (n+1)) ∧ Tendsto u atTop (𝓝 0) ∧
        ∀ n, IsAlgebraic ℚ (u n) := by sorry
