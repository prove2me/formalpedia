-- Prove2me | Theorems.Thm_CatalyticMatching_General_threshold_or_matching
-- name    : CatalyticMatching.General.threshold_or_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:43.814083+00:00
-- url     : https://prove2.me/theorems/c8221e5e-892c-42b1-9ceb-79c91377c0f6
-- title:
--   Lemma 3.10 — threshold-or-matching dichotomy
-- statement:
--   Let $G$ have a perfect matching, let $T'$ be a rational Tutte evaluation of rank $n$, and let $W:E\to\mathbb N$ be arbitrary. Form $A$, $A_e$, $P_{0,e}$, $P_{1,e}$ and the coefficient sums as defined on pages 17–18. The nonzero polynomial $\operatorname{Pf}(A)$ has a least nonzero degree $w_0$, and
--
--   $$\bigl(\exists e:\ P_{0,e},P_{1,e}\ne0,\quad W(e)+w_e=w_{\bar e},\quad\operatorname{Pf}(A_e)=P_{0,e}+yP_{1,e}\bigr)$$
--   $$\lor\ \bigl(M=\{e:c_{w_0}^{\bar e}=0\}\text{ is a perfect matching, and }M=\{e:[z^{w_0}]P_{0,e}=0\}\bigr).$$
--
--   Here $w_e$ and $w_{\bar e}$ are the least nonzero degrees of their respective components. Component polynomials may vanish, and the first branch requires actual degrees of both. Cancellation and zero evaluated edge entries are permitted. Neither branch assumes a unique or a minimum-weight matching.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled graph or matrix → vertices and indices in Fin n, with arbitrary n; reason: relabeling covers every finite instance, including n=0 and n=1
--   - encoding: w₀ is the least nonzero Pfaffian degree, with component least degrees only if they exist → leastDegree returns Option ℕ, and the conclusion produces w₀ and explicit nonzero component degrees; reason: zero polynomials have no fictitious degree; full rank implies existence of w₀ without an extra hypothesis
--   - encoding: W(e)=w_bar(e)-w_e → W(e)+w_e=w_bar(e); reason: avoids truncated natural subtraction and is equivalent to the printed equality over integers
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 3.10, printed p.19 = PDF p.19

import Definitions.Def_CatalyticMatching_General_WeightedPfaffian

namespace CatalyticMatching.General

/-- Lemma 3.10 p.19, proof pp.19--20, standing setup pp.17--18. Least degrees are absent on zero polynomials; no isolation or noncancellation hypothesis. -/
theorem threshold_or_matching {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M)
    (a : G.edgeSet → ℚ) (hfull : (tutteEval G a).rank = n) (W : G.edgeSet → ℕ) :
    ∃ w0 : ℕ, leastDegree (pfaffian (weightedMatrix G a W)) = some w0 ∧
      ((∃ (e : G.edgeSet) (we wb : ℕ),
        leastDegree (P0 G a W e) = some wb ∧
        leastDegree (P1 G a W e) = some we ∧ W e + we = wb ∧
        pfaffian (edgeMatrix G a W e) =
          Polynomial.C (P0 G a W e) + Polynomial.X * Polynomial.C (P1 G a W e)) ∨
      (MulmuleyVV.Matching.IsPerfectMatchingEdges G (coefficientMatching G a W w0) ∧
        ∀ e : G.edgeSet, e ∈ coefficientMatching G a W w0 ↔ (P0 G a W e).coeff w0 = 0)) := by sorry

end CatalyticMatching.General
