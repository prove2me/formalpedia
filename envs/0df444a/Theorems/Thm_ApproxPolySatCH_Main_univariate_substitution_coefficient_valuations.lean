-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_univariate_substitution_coefficient_valuations
-- name    : ApproxPolySatCH.Main.univariate_substitution_coefficient_valuations
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:32:58.181283+00:00
-- url     : https://prove2.me/theorems/d82b12f0-826c-4113-b5e6-e2ea5a77e535
-- title:
--   Lemma 12 — Coefficient and valuation transport under Kronecker substitution
-- statement:
--   Let $k$ be a field, let $\nu$ be an epsilon-adic valuation on the valued closure $L$, and let $P\in k[T,W,\varepsilon,Z]$ be nonzero with individual $T$, $W$, and $\varepsilon$ degrees at most $D_0$. Put $m=D_0+1$ and define
--   $$P_2=\operatorname{TT}_W\operatorname{TT}_T P,\qquad \widehat P=P(\varepsilon^{m^2},\varepsilon^m,\varepsilon,Z).$$
--
--   The substituted polynomial is nonzero, as is $P_2$. Moreover, there is $N\in\mathbb N$ such that every nonzero coefficient of $P_2(\varepsilon,Z)$ has valuation at most $D_0$, and at every such exponent $i$ the two coefficients satisfy
--   $$\nu(\widehat P_i)=\nu((P_2)_i)+N.$$
--   If instead $(P_2)_i=0$, then $\nu(\widehat P_i)>N+D_0$, including the case where $\widehat P_i=0$ and its valuation is $\infty$.
--
--   This packages the coefficient identities (22) and (23) of Lemma 12 together with their consequences outside the low coefficient band. The integer $N$ represents the fixed $T,W$ exponent contribution $a_0m^2+b_0m$; all comparisons are in $\mathbb Q\cup\{\infty\}$. The case $D_0=0$ is included, and there is no degree restriction on $Z$.
--
--   **Formalization Note.** The polynomials $P_2$ and $\widehat P$ are converted by `asZPolynomial` into univariate polynomials over the published valued closure. The conclusion quantifies over all natural-number coefficient indices, so the out-of-band assertion also covers coefficients outside the original sparse support.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Lemma 12, p.22, especially equations (22)–(23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=22

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.univariate_substitution_coefficient_valuations {k : Type} [Field k]
    (v : EpsilonValuation k) (P : Poly k 4) (hP : P ≠ 0) (D0 : ℕ)
    (hT : MvPolynomial.degreeOf 0 P ≤ D0) (hW : MvPolynomial.degreeOf 1 P ≤ D0)
    (heps : MvPolynomial.degreeOf 2 P ≤ D0) :
    let P2 := asZPolynomial (twiceTrailing (MvPolynomial.map (algebraMap k (Constants k)) P))
    let Phat := asZPolynomial (MvPolynomial.map (algebraMap k (Constants k))
      (kroneckerSubstitution D0 P))
    kroneckerSubstitution D0 P ≠ 0 ∧ P2 ≠ 0 ∧ ∃ N : ℕ,
      (∀ i, P2.coeff i ≠ 0 →
        v.val (P2.coeff i) ≤ (D0 : WithTop ℚ) ∧
          v.val (Phat.coeff i) = v.val (P2.coeff i) + (N : WithTop ℚ)) ∧
      (∀ i, P2.coeff i = 0 →
        ((N + D0 : ℕ) : WithTop ℚ) < v.val (Phat.coeff i)) := by sorry
