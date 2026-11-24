-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_Supplement_theorem_4_3
-- name    : FeasibleBasesHC.Structure.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:32:39.272576+00:00
-- url     : https://prove2.me/theorems/55254497-882c-410f-a9e0-d1ca8aec2863
-- title:
--   Theorem 4.3 — even-node feasibility criterion (corrected: n ≥ 5)
-- statement:
--   Let $(s,\pi,L,U)$ be an encoded quadruple as specified in §4, p. 15, and let $\Gamma(G)$ denote the ultimate feasible bases (feasible for all discount factors sufficiently close to $1$ from below). Let $n=2k$ and $n\ge5$ (hence $k\ge3$). Its basis is ultimate feasible if and only if
--
--   $$|U|=|L|=k-1,\qquad \pi(s)\in U,\qquad s-1\in R\cup U,$$
--
--   and there exists the first-passage index $i^*$ of Remark 2 such that
--
--   $$\left|I(i^*)\setminus\{1,\pi^{-1}(1)\}\right|\ge\frac{n-4}{2},$$
--   $$N_{UL}(i)+N_{UR}(i)+N_{RL}(i)\le N_{LU}(i)+1\qquad\bigl(i\in I(s-2)\setminus I(i^*)\bigr).$$
--
--   This companion theorem is the even-node exact criterion, including all five conditions and both implications. The added bound repairs the printed statement: at $n=4$, $s=4$, $\pi=(1\ 3\ 4\ 2)$, $L=\{2\}$ and $U=\{3\}$ give a basis feasible for every $0<\beta<1$, but $\pi(s)=2\notin U$. Its nonzero flows are $x_{13}=1$, $x_{34}=\beta$, $x_{42}=\beta^2$, $x_{21}=\beta^3$, and $y_4=\beta^2(1-\beta)$; its determinant is $\beta^3(\beta-1)$. The proof on p. 22 applies Theorem 4.1, whose hypothesis is $n\ge5$.
--
--   **Formalization Note** The encoded basis, cyclic coefficients, and first-passage predicate are shared with every statement in this supplement. All flows and discounts are real, exactly as in the published base setting.
--
--   Differences from the source:
--   - encoding: Nodes are labelled 1 through n, with cyclic index arithmetic → Fin n with paper node i represented by i-1 and [NeZero n]; reason: The root is 0, the final node is -1, and no defined source instance is excluded
--   - reading: Feasible bases in the scope fixed on p. 6 → Membership in the published GamUlt for some loopless ambient graph containing the encoded arcs; reason: Feasible means eventually feasible as beta approaches 1 from below; nonbasic flows vanish, so all such ambient graphs give the same feasibility condition
--   - reading: The thin-arc bullet on p. 15 excludes s, while the displayed B and eta_i exclude s-1 → Use the displayed B: thin arcs (i,pi(i-1)) for i different from s; reason: This resolves the inconsistent descriptions using the displayed basis and the variable domain on pp. 15–16; the bullet otherwise includes the loop (s,s)
--   - correction: Theorem 4.3 is printed for all even n → Add 5 <= n, equivalently k >= 3; reason: The printed theorem fails at n=4 for s=4, pi=(1 3 4 2), L={2}, U={3}; the source proof applies Theorem 4.1 on p. 22, which requires n>=5. This excludes the false n=4 case; n=2 has no encoded quadruple. See DISPROOF.md
--   - encoding: Conditions (iv) and (v) use the index i* defined by Remark 2 → An existential index satisfying IsIStar and both remaining conditions; reason: Under (ii) and (iii), Remark 2 makes the index exist uniquely; no choice default is introduced
--   - encoding: The lower bound on the size of I(i*) minus the two distinguished indices is (n-4)/2 → n-4 <= 2*card in the integers, with the two indices 0 and pi.symm 0; reason: For even n at least 6 this is the identical bound; using integer arithmetic avoids truncated subtraction
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 22, Theorem 4.3

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts

namespace FeasibleBasesHC.Structure.Supplement

theorem theorem_4_3 {n : ℕ} [NeZero n] (k : ℕ)
    (heven : n = 2 * k) (hn : 5 ≤ n) (q : Quadruple n) :
    q.Feasible ↔
      (q.U.card = k - 1 ∧ q.L.card = k - 1) ∧
      q.pi q.s ∈ q.U ∧ q.s - 1 ∈ R n ∪ q.U ∧
      ∃ iStar : Fin n, IsIStar q iStar ∧
        (n : ℤ) - 4 ≤ 2 * ((I q iStar \ {0, q.pi.symm 0}).card : ℤ) ∧
        ∀ i ∈ I q (q.s - 2) \ I q iStar,
          downCount q i ≤ N q q.L q.U i + 1 := by sorry

end FeasibleBasesHC.Structure.Supplement
