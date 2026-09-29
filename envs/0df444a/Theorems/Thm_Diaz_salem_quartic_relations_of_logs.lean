-- Prove2me | Theorems.Thm_Diaz_salem_quartic_relations_of_logs
-- name    : Diaz.salem_quartic_relations_of_logs
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T14:37:59.556025+00:00
-- url     : https://prove2.me/theorems/e43899ea-bd36-452e-85ae-3bd7c5db5c62
-- title:
--   Quadratic relations between a real and a purely imaginary logarithm of algebraic numbers, unconditionally
-- statement:
--   **Quadratic relations between a real and a purely imaginary logarithm, unconditionally.**
--
--   Let $t \neq 0$ be real and $s \neq 0$ purely imaginary, and suppose $\mathrm{e}^{t}$ and $\mathrm{e}^{s}$ are algebraic. If $A, B, C \in \mathbb{Q}$ satisfy
--
--   $$A t^2 + B\, t s + C s^2 = 0,$$
--
--   then $A = B = C = 0$.
--
--   This is `Diaz.salem_quartic_relations` with its hypothesis `hGS` discharged. That node assumes, for arbitrary $t$ and $s$, that an algebraic $s/t$ is rational; that is not true for arbitrary complex numbers, so the present statement restricts to logarithms of algebraic numbers, where it is the Gelfond–Schneider theorem. If $s/t$ were algebraic and irrational, then $\mathrm{e}^{s} = \mathrm{e}^{(s/t)\,t}$ would be transcendental by `Schanuel.gelfond_schneider`, contrary to hypothesis.
--
--   The hypotheses are satisfiable, for instance by $t = \log 2$ and $s = i\pi$, where the conclusion says that $\pi^2 / (\log 2)^2$ is irrational.
--
--   **Novelty.** None claimed. The quadratic step is elementary and the transcendence input is classical (Gelfond 1934, Schneider 1934).
-- source:
--   C. Perassi, unpublished apart from this node and Diaz.salem_quartic_relations. Background: A. O. Gelfond (1934) and Th. Schneider (1934); formal proof of Gelfond-Schneider by M. Karatarakis and F. Wiedijk, arXiv:2603.24823.

import Mathlib

theorem Diaz.salem_quartic_relations_of_logs {t s : ℂ} (ht : t ≠ 0) (hs : s ≠ 0)
    (htR : t.im = 0) (hsI : s.re = 0)
    (het : IsAlgebraic ℚ (Complex.exp t)) (hes : IsAlgebraic ℚ (Complex.exp s))
    {A B C : ℚ} (h : (A : ℂ) * t ^ 2 + (B : ℂ) * (t * s) + (C : ℂ) * s ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by sorry
