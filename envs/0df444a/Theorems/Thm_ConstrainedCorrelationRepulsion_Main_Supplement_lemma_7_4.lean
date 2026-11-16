-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_Supplement_lemma_7_4
-- name    : ConstrainedCorrelationRepulsion.Main.Supplement.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:42.881794+00:00
-- url     : https://prove2.me/theorems/5b465b60-8438-4b81-bd73-97b686aa951f
-- title:
--   Lemma 7.4 — direct quadratic-time clique extraction
-- statement:
--   There is an absolute positive constant $C$ such that for every finite simple graph $G$ with $n$ vertices, every integer $t>0$ and every cluster-deletion set $D$ of $G\vee K_t$, the direct universal-row scan returns a clique $K$ of $G$ with
--
--   $$|K|\ge n-\frac{|D|}{t},\qquad T\le C(n+t)^2.$$
--
--   The input deletion set is arbitrary: it need not be optimal, approximately optimal, or preserve the universal clique. The bound uses real division, including when its right-hand side is negative. The scan's maintained population count equals its output bitmap cardinality. Its complexity constant is quantified before every graph, size and deletion set. This is the constructive extraction used by Theorem 1.3.
--
--   Differences from the source:
--   - encoding: one can produce a clique in quadratic time → the specified costed universal-row scan returns that clique and its population counter agrees with the output cardinality; reason: a row of a surviving universal vertex is exactly its cluster on valid inputs; explicit scan costs express the source word-operation bound
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Lemma 7.4 and proof, printed p.36 (PDF p.37)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Scan

namespace ConstrainedCorrelationRepulsion.Main.Supplement

/-- Lemma 7.4, printed p.36 / PDF p.37. A universal constant bounds the actual scan,
before quantification over all inputs. The size bound uses real, untruncated division. -/
theorem lemma_7_4 : ∃ C : ℕ, 0 < C ∧
    ∀ n t : ℕ, 0 < t → ∀ G : Graph n,
      ∀ D : Finset (Sym2 (Fin (n+t))), IsDeletionSet (joinClique G t) D →
        G.IsClique (extractedClique n t D) ∧
        (n : ℝ) - (D.card : ℝ) / (t : ℝ) ≤ ((extractedClique n t D).card : ℝ) ∧
        (gatherScan n t D).size = (extractedClique n t D).card ∧
        (gatherScan n t D).work ≤ C * (n+t)^2 := by sorry

end ConstrainedCorrelationRepulsion.Main.Supplement
