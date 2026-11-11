-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_4_3
-- name    : AcceptSubcube.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:58:39.496822+00:00
-- url     : https://prove2.me/theorems/c722f771-0bd5-470f-8a1a-f65055139d2e
-- title:
--   Lemma 4.3 — majority repair: $C_{\mathcal I}(y)\le 3\,\mathrm{OPT}_{\tau,r}+32k^2D_2(n)r^2$
-- statement:
--   Let $k\ge2$. There is a deterministic polynomial-time algorithm that, given a $k$-uniform instance $\mathcal I$ on $n$ variables with at most one unweighted predicate per $k$-scope (not necessarily complete, predicates arbitrary), a center $\tau$ and a radius $1\le r\le n$, returns an assignment $y$ with
--   $$C_{\mathcal I}(y)\le 3\,\mathrm{OPT}_{\tau,r}+32k^2D_2(n)\,r^2 .$$
--
--   The output need not lie in the ball. This is the quadratic repair used when the residual arity is $2$.
--
--   Differences from the source:
--   - reading: a deterministic polynomial-time algorithm → a TM2 polynomial-time map (I, τ, r) ↦ y, τ given as n bits, the polynomial depending on k; reason: the paper names no machine model; k is fixed
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.3, p.16

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

/-- **Lemma 4.3 (Majority repair).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.3, p.16: "For k ≥ 2, at most one
unweighted predicate per k-scope, and 1 ≤ r ≤ n, a deterministic polynomial-time algorithm returns
y with C_I(y) ≤ 3 OPT_{τ,r} + 32k² D₂(n) r². (9)"

**Formalization Note.** §4's setting (p.15): the instance is arbitrary (well formed, `k`-uniform, at
most one predicate per scope; not necessarily complete, predicates arbitrary). The machine reads
`(I, τ, r)` (`τ` as a list of `n` bits); the polynomial may depend on `k`. The output need not lie
in the ball. -/
theorem lemma_4_3 (k : ℕ) (hk : 2 ≤ k) :
    ∃ rep : GInst × List Bool × ℕ → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encBall encAssign rep) ∧
      ∀ I : GInst, I.WellFormed → I.Uniform k → I.ScopeUnique →
        ∀ τ : Fin I.n → Bool, ∀ r : ℕ, 1 ≤ r → r ≤ I.n →
          cost I (asg I (rep (I, List.ofFn τ, r))) ≤
            3 * OPTball I τ r + 32 * k ^ 2 * Dj k 2 I.n * r ^ 2 := by sorry

end AcceptSubcube
