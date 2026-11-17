-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_6_3
-- name    : CoRSuccGap.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:41:59.146662+00:00
-- url     : https://prove2.me/theorems/6ef20ee9-62eb-43fc-aafc-a8b050654f5d
-- title:
--   Theorem 6.3 -- exact two-sided CoR term-size bounds for $G_k$
-- statement:
--   For every $k\ge1$, every CoR term agreeing with $G_k$ on all finite nonempty structures has at least
--
--   $$
--   2k\,2^k-1
--   $$
--
--   syntax-tree nodes. Conversely, there is a CoR term with exactly
--
--   $$
--   (2k+6)2^k-5
--   $$
--
--   nodes that is equivalent to $G_k$ on every nonempty structure, finite or infinite. All input, constant, Boolean, converse and composition nodes are counted, with repeated subterms counted per occurrence.
--
--   Differences from the source:
--   - generalization: the first sentence is phrased for $T\equiv G_k$ and then says the lower bound still holds under finite agreement → Lean states the explicitly stronger finite-agreement form directly; reason: this is a clause of the theorem itself.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 6.3, p.34 (PDF 36)

import Definitions.Def_CoRSuccGap_Gk
import Definitions.Def_CoRSuccGap_Supplement_TermSize

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 6.3 (Term size).** Uezato--Nakamura, *An Exponential Succinctness Gap between
Three-Variable Logic and the Calculus of Relations*, arXiv:2609.26778 (held version, sha256
5ad6337d…c9b6), Theorem 6.3, p.34 (PDF 36).

For every `k ≥ 1`, any CoR term agreeing with `G_k` on all finite nonempty structures has at
least `2k·2^k-1` syntax-tree nodes.  Conversely, one term has exactly `(2k+6)2^k-5` nodes and
agrees with `G_k` on every nonempty structure, finite or infinite.

**Formalization Note.** `Term.numNodes` counts all tree nodes, not composition occurrences or
distinct DAG gates.  The positive hypothesis `k ≥ 1` keeps both displayed natural-number
subtractions in their intended, nontruncated regime. -/
theorem theorem_6_3 (k : ℕ) (hk : 1 ≤ k) :
    (∀ T : CoRSuccGap.Term (GSym k),
      (∀ (D : Type) [Fintype D] [Nonempty D] (M : GSym k → D → D → Prop),
        T.eval M = Gk k M) →
      2 * k * 2 ^ k - 1 ≤ Supplement.Term.numNodes T) ∧
    ∃ T : CoRSuccGap.Term (GSym k),
      (∀ (D : Type) [Nonempty D] (M : GSym k → D → D → Prop),
        T.eval M = Gk k M) ∧
      Supplement.Term.numNodes T = (2 * k + 6) * 2 ^ k - 5 := by sorry

end Supplement
end CoRSuccGap
