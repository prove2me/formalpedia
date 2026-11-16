-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_Supplement_proposition_7_2
-- name    : ConstrainedCorrelationRepulsion.Main.Supplement.proposition_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:10.029576+00:00
-- url     : https://prove2.me/theorems/153dd411-db03-4f19-bff3-bfc79b9a9364
-- title:
--   Proposition 7.2 — both join optimum bounds and strictness
-- statement:
--   Let $G$ be any finite simple graph with $n$ vertices, $m>0$ edges and maximum clique size $\omega(G)$. For every positive integer $t$, join $G$ to a new universal clique $K_t$. Its minimum cluster-deletion cost satisfies
--
--   $$\operatorname{OPT}_{\rm del}(G\vee K_t)\le t(n-\omega(G))+m-\binom{\omega(G)}2\le t(n-\omega(G))+m.$$
--
--   The second displayed inequality is strict. The formal statement retains both the weak inequality and its strict version. This upper bound is used in the exact approximation transfer, and its optimum is the existing constrained objective on the cluster-deletion embedding.
--
--   Differences from the source:
--   - encoding: finite unsigned graphs, deletion optimum and displayed subtraction → Mathlib simple graphs on labelled vertices, published constrained OPT through the deletion embedding, and real arithmetic; reason: the labelling changes no instance, the embedding counts exactly deleted original edges, and real subtraction avoids natural-number truncation
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Proposition 7.2, printed p.35 (PDF p.36)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Graphs

namespace ConstrainedCorrelationRepulsion.Main.Supplement

/-- Proposition 7.2, printed p.35 / PDF p.36, including the binomial term and strictness. -/
theorem proposition_7_2 {n : ℕ} (G : Graph n) (t : ℕ) (ht : 0 < t)
    (hm : 0 < edgeCount G) :
    (deletionOPT (joinClique G t) : ℝ) ≤
      (t : ℝ) * ((n : ℝ) - (omega G : ℝ)) + (edgeCount G : ℝ) -
        (Nat.choose (omega G) 2 : ℝ) ∧
    (t : ℝ) * ((n : ℝ) - (omega G : ℝ)) + (edgeCount G : ℝ) -
        (Nat.choose (omega G) 2 : ℝ) ≤
      (t : ℝ) * ((n : ℝ) - (omega G : ℝ)) + (edgeCount G : ℝ) ∧
    (t : ℝ) * ((n : ℝ) - (omega G : ℝ)) + (edgeCount G : ℝ) -
        (Nat.choose (omega G) 2 : ℝ) <
      (t : ℝ) * ((n : ℝ) - (omega G : ℝ)) + (edgeCount G : ℝ) := by sorry

end ConstrainedCorrelationRepulsion.Main.Supplement
