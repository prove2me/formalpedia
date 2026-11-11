-- Prove2me | Theorems.Thm_ApproxCountRwPHP_Unprovability_theorem_2_1
-- name    : ApproxCountRwPHP.Unprovability.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:52.889727+00:00
-- url     : https://prove2.me/theorems/4931b052-3704-4740-9fdf-d1200ae0e33d
-- title:
--   Theorem 2.1 — Herbrand finite instance form
-- statement:
--   Let K be any first-order language with equality and at least one constant symbol, and T any universal theory in K. Let c̄ be any finite, possibly empty tuple of fresh constants. Let χ(c̄,x̄) be quantifier-free. If T entails ∃x̄ χ(c̄,x̄), there are finitely many actual axiom matrices θj of T, ground substitutions s̄j(c̄), and ground witness tuples t̄i(c̄) such that
--
--   $$\models\left(\bigwedge_{j=1}^{m}\theta_j(\bar s_j(\bar c))\right)\longrightarrow\left(\bigvee_{i=1}^{r}\chi(\bar c,\bar t_i(\bar c))\right).$$
--
--   All terms belong to K(c̄), and every axiom matrix is quantifier-free. Empty conjunction and disjunction are permitted. This preserves the finite axiom-instance conclusion, rather than merely asserting finitely many witness terms.
--
--   Differences from the source:
--   - encoding: first-order derivability with equality → semantic consequence and validity in Mathlib; reason: Gödel completeness identifies these notions for the source statements
--   - encoding: finite tuples of parameters, axioms and terms → Fin-indexed tuples and explicitly stored axiom matrices; reason: these record exactly the same finite instances, including empty tuples
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Theorem 2.1, printed p. 14, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=16

import Definitions.Def_ApproxCountRwPHP_Unprovability_HerbrandSyntax

open FirstOrder

namespace ApproxCountRwPHP.Unprovability

/-- Theorem 2.1, finite-instance Herbrand theorem, printed 14 / PDF 16.
The fresh parameter tuple may be empty; the required constant is in K itself.
Both provability assertions use semantic consequence, by completeness. -/
theorem theorem_2_1 (K : Language) (T : K.Theory) [T.IsUniversal]
    [Nonempty K.Constants] (p k : ℕ) (χ : K[[Fin p]].BoundedFormula Empty k)
    (hχ : χ.IsQF)
    (hproof : (K.lhomWithConstants (Fin p)).onTheory T ⊨ᵇ χ.exs) :
    ∃ (m r : ℕ) (axioms : Fin m → UniversalAxiom T)
      (ss : (j : Fin m) → Fin (axioms j).variableCount → K[[Fin p]].Term Empty)
      (ts : Fin r → Fin k → K[[Fin p]].Term Empty),
      (∅ : K[[Fin p]].Theory) ⊨ᵇ
        ((conjunction (List.ofFn (fun j => axiomGroundInstance (axioms j) (ss j)))).imp
          (disjunction (List.ofFn (fun i => groundSubstitution χ (ts i))))) := by sorry

end ApproxCountRwPHP.Unprovability
