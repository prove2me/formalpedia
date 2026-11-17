-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_5_1
-- name    : CoRSuccGap.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:40:42.007694+00:00
-- url     : https://prove2.me/theorems/e28f9a3b-c481-4bbc-8090-f7f9b8646f7f
-- title:
--   Theorem 5.1 -- fixed-vocabulary $FO^3$ and relational-circuit succinctness
-- statement:
--   There are absolute constants $c>0$ and $m_0$ such that for every $m\ge m_0$ there is an $FO^3$ binary query over one binary relation, of syntax-tree size at most $m$, for which every relational circuit agreeing on all finite nonempty structures has at least
--
--   $$
--   2^{c m/\log m}
--   $$
--
--   composition gates. Conversely, for every fixed finite binary vocabulary $\sigma$, there are a compiler, $C_\sigma>0$ and $m_\sigma$ such that every size-$m\ge m_\sigma$ $FO^3[\sigma]$ formula with at most the two output variables free compiles to an equivalent relational circuit of total size at most $2^{C_\sigma m/\log m}$ in at most the same number of construction steps. The compiled circuit is correct on every nonempty structure.
--
--   Here $\log m=\max\{\log_2m,1\}$. The lower constants are chosen before $m$; the upper constants may depend only on the fixed vocabulary.
--
--   Differences from the source:
--   - encoding: the source uses $2^{\Omega(m/\log m)}$ and $2^{O_\sigma(m/\log m)}$ notation → Lean expands both into positive constants and eventual thresholds with the source's dependency order; reason: makes the asymptotic claims proposition-valued without choosing an unsupported numerical constant.
--   - encoding: constructibility is stated algorithmically in prose → Lean packages a compiler function, its output circuit, semantic correctness, and a natural-number construction-cost witness; reason: records the constructive clause explicitly.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 5.1, p.28 (PDF 30), proof pp.28--31 (PDF 30--33)

import Definitions.Def_CoRSuccGap_Supplement_FiniteVariableLogic

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 5.1 (Fixed-vocabulary succinctness).** Uezato--Nakamura, *An Exponential
Succinctness Gap between Three-Variable Logic and the Calculus of Relations*, arXiv:2609.26778
(held version, sha256 5ad6337d…c9b6), Theorem 5.1, p.28 (PDF 30).

There are absolute positive constants and a threshold such that every larger syntax-size budget
`m` contains a one-binary-relation FO³ query for which every relational circuit agreeing on every
finite nonempty structure has at least `2^(c m / log m)` composition gates.  Conversely, for each
fixed finite binary vocabulary there is a compiler and vocabulary-dependent positive constant and
threshold: every FO³ formula with only the two output variables free compiles to an equivalent
relational circuit of total size, and in construction time, at most `2^(C m / log m)`.

**Formalization Note.** `paperLog m = max(log₂ m,1)`.  The lower constants precede `m` and are
absolute.  The upper compiler and constants are quantified only after the fixed vocabulary, so
they may depend on it and on nothing about the input formula.  Lower correctness is on finite
nonempty structures; compiler correctness is on all nonempty structures, finite or infinite. -/
theorem theorem_5_1 :
    (∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ p : FOFormula PUnit (Fin 3),
        p.freeVars ⊆ ({0, 1} : Finset (Fin 3)) ∧ p.numNodes ≤ m ∧
        ∀ C : Circuit PUnit,
          (∀ (D : Type) [Fintype D] [Nonempty D] (M : PUnit → D → D → Prop),
            C.eval M = p.query3 M) →
          Real.rpow 2 (c * (m : ℝ) / paperLog m) ≤ (C.numCompGates : ℝ)) ∧
    (∀ (σ : Type) [Fintype σ], ∃ A : FO3Compiler σ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ m₀ : ℕ, ∀ p : FOFormula σ (Fin 3),
        p.freeVars ⊆ ({0, 1} : Finset (Fin 3)) → m₀ ≤ p.numNodes →
        ((A.circuit p).size : ℝ) ≤
            Real.rpow 2 (C₀ * (p.numNodes : ℝ) / paperLog p.numNodes) ∧
        (A.constructionTime p : ℝ) ≤
            Real.rpow 2 (C₀ * (p.numNodes : ℝ) / paperLog p.numNodes)) := by sorry

end Supplement
end CoRSuccGap
