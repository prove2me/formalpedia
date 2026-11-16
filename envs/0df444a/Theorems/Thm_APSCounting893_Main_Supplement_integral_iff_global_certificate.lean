-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_integral_iff_global_certificate
-- name    : APSCounting893.Main.Supplement.integral_iff_global_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:11:47.742511+00:00
-- url     : https://prove2.me/theorems/a6d66cf3-9034-4f27-b4c6-de6cff09a3b4
-- title:
--   Theorem 7.5 — Integrality iff a global polynomial certificate exists
-- statement:
--   Let $f,f_1,\ldots,f_m\in\mathbb C[x_1,\ldots,x_n]$ and $A=\mathbb C[f_1,\ldots,f_m]$, with $u$ independent. Then
--
--   $$f\text{ integral over }A\quad\Longleftrightarrow\quad\exists Q\in\mathbb C[Y,U,V]:\ Q(f_1,\ldots,f_m,u,1-uf)=0,\quad Q(Y,0,0)=1.$$
--
--   Both equalities are polynomial identities. Integrality independently means a monic equation of positive degree over the generated subalgebra; it is not defined using this equivalence. This identifies exactly the certificates needed for the degree bound and decision reduction.
--
--   Differences from the source:
--   - encoding: polynomial identities with named Y,U,V variables → GlobalCertificate over a disjoint-sum variable type and Mathlib IsIntegral over Algebra.adjoin; reason: all variables are independent, and the slice equality holds as a polynomial in every Y
--   - encoding: the section dismisses f=0 as always integral → the zero-target case is included directly; reason: it has certificate V-1 multiplied by -1, namely 1-V; the source reduction separately handles this same case
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 7.5, p. 29

import Definitions.Def_APSCounting893_Main_Supplement_Certificates

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 7.5, including the harmless f=0 case dismissed at the section's start. -/
theorem integral_iff_global_certificate (n m : ℕ) (F : PolynomialMap ℂ n m)
    (f : Polynomials ℂ n) :
    IntegralOverGenerators F f ↔ ∃ Q : Certificate ℂ m, GlobalCertificate F f Q := by sorry

end APSCounting893.Main.Supplement
