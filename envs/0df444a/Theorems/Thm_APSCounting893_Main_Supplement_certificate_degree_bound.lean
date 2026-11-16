-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_certificate_degree_bound
-- name    : APSCounting893.Main.Supplement.certificate_degree_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:12:24.363446+00:00
-- url     : https://prove2.me/theorems/1c304985-0a18-486a-8e96-7b7a4895588a
-- title:
--   Theorem 7.7 — Exact certificate degree bound and rational coefficients
-- statement:
--   Let $f,f_1,\ldots,f_m\in\mathbb C[x_1,\ldots,x_n]$, assume $f$ integral over $A=\mathbb C[f_i]$, and set $\rho=\operatorname{trdeg}_{\mathbb C}\mathbb C(f_1,\ldots,f_m)$ and $\Delta=\max\{\deg f_i,\deg f+1\}$. There is a certificate $Q$ satisfying both identities of Theorem 7.5 with
--
--   $$\deg Q\le(\rho+2)\Delta^{\rho+1}.$$
--
--   Here degree is the total degree in all $Y,U,V$ variables. If the input polynomials have rational coefficients, such a certificate can be chosen over $\mathbb Q$ with the same bound. The rational clause is a second conjunct, under equality with rational coefficient lifts; no rationality restriction is placed on the first conjunct. This supplies the exact effective bound, including $\rho=0$.
--
--   Differences from the source:
--   - encoding: transcendence degree of the generated rational-function field → finite cardinal transcendence degree of FractionRing (Algebra.adjoin), converted to a natural number; reason: the generated domain is finitely generated, so this cardinal is finite and the conversion loses no value
--   - encoding: rational input polynomials admit rational Q → every rational tuple lifting to the given complex tuple has a rational GlobalCertificate of the same bound; reason: explicit coefficient maps encode rationality and retain both certificate identities
--   - encoding: the section handles zero targets and empty or constant data separately → totalDegree 0=0, empty maximum=0, and Delta at least one; reason: the zero-target case has degree-one certificate 1-V, so these conventions include the source padding cases without an undefined degree
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 7.7, p. 30

import Definitions.Def_APSCounting893_Main_Supplement_Certificates

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 7.7: the exact rank-sensitive total-degree bound and rational descent. -/
theorem certificate_degree_bound (n m : ℕ) (F : PolynomialMap ℂ n m)
    (f : Polynomials ℂ n) (hint : IntegralOverGenerators F f) :
    (∃ Q : Certificate ℂ m, GlobalCertificate F f Q ∧ Q.totalDegree ≤ certificateBound F f) ∧
    (∀ (Fq : PolynomialMap ℚ n m) (fq : Polynomials ℚ n),
      (∀ i, MvPolynomial.map (algebraMap ℚ ℂ) (Fq i) = F i) →
      MvPolynomial.map (algebraMap ℚ ℂ) fq = f →
      ∃ Qq : Certificate ℚ m, GlobalCertificate Fq fq Qq ∧
        Qq.totalDegree ≤ certificateBound F f) := by sorry

end APSCounting893.Main.Supplement
