-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_univariate_substitution
-- name    : ApproxPolySatCH.Main.univariate_substitution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:13:16.520042+00:00
-- url     : https://prove2.me/theorems/0f86178b-4124-4213-9f05-78ad45cecf1d
-- title:
--   Lemma 12 — Strict valuation test under substitution
-- statement:
--   Let $k$ be a field and let $\nu$ be an epsilon-adic valuation on $L$. Let $P\in k[T,W,\varepsilon,Z]$ be nonzero and have individual degree at most $D_0$ in each of T, W and epsilon. There is no bound on Z-degree. Put $b=D_0+1$ and
--   $$P_2=\operatorname{TT}_W\operatorname{TT}_T P,\qquad\widehat P=P(\varepsilon^{b^2},\varepsilon^b,\varepsilon,Z).$$
--   Then $\widehat P\ne0$ and
--   $$\nu(P_2(\varepsilon,Z))<\nu(P_2(\varepsilon,0))\iff\nu(\widehat P(\varepsilon,Z))<\nu(\widehat P(\varepsilon,0)).$$
--   Polynomial valuations are Gauss valuations and scalar zero has valuation infinity, so zero constant terms are included. The case $D_0=0$ is retained.
--
--   This transfers the exact strict valuation test through a sparse univariate substitution.
--
--   Differences from the source:
--   - generalization: The coefficient field is rational or finite. → The algebraic statement is quantified over every field, with the stated algebraic closures and valuation where used.; reason: The algebraic arguments use no restriction on the base field; specializing to a rational or finite field gives the entire source statement.
--   - encoding: Individual degree bounds in T,W,epsilon; no Z-degree bound; D0 may be zero. → Four finite variable indices and b=D0+1 with exponents b squared and b, evaluated in the valued closure.; reason: This retains nonvanishing and the entire strict-valuation equivalence, including infinite scalar valuation when the constant term is zero.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Lemma 12, p.22 (PDF p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=22

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem univariate_substitution {k : Type} [Field k] (v : EpsilonValuation k)
    (P : Poly k 4) (hP : P ≠ 0) (D0 : ℕ)
    (hT : MvPolynomial.degreeOf 0 P ≤ D0) (hW : MvPolynomial.degreeOf 1 P ≤ D0)
    (heps : MvPolynomial.degreeOf 2 P ≤ D0) :
    kroneckerSubstitution D0 P ≠ 0 ∧
      (let P2 := asZPolynomial (twiceTrailing (MvPolynomial.map (algebraMap k (Constants k)) P))
       let Phat := asZPolynomial (MvPolynomial.map (algebraMap k (Constants k))
         (kroneckerSubstitution D0 P))
       gaussValuation v P2 < v.val (P2.eval 0) ↔
         gaussValuation v Phat < v.val (Phat.eval 0)) := by sorry

end ApproxPolySatCH.Main
