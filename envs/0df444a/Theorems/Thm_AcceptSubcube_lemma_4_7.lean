-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_4_7
-- name    : AcceptSubcube.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:49.928173+00:00
-- url     : https://prove2.me/theorems/bd86ab64-030a-45d6-8b3e-6eabdbe638fe
-- title:
--   Lemma 4.7 — exactly feasible near-optimal rational points of (10)–(14)
-- statement:
--   Let $k\ge3$. There is an algorithm, polynomial-time for each fixed $k$, which, given a $k$-uniform instance $\mathcal I$ with at most one predicate per scope on $n\ge k$ variables, a center $\tau$, a radius $k\le r\le n$ and a positive rational $\epsilon_{\mathrm{num}}$, outputs a rational point (moment vector) of the relaxation (10)–(14) of the instance XORed with $\tau$ that is **exactly** feasible, including $Z\succeq0$, and has objective
--   $$L\le\mathrm{OPT}_{\tau,r}+\epsilon_{\mathrm{num}} .$$
--
--   For inverse-polynomial $\epsilon_{\mathrm{num}}$ the time is $n^{O_k(1)}$. Exact feasibility is what the charging argument of Lemma 4.4 needs.
--
--   Differences from the source:
--   - generalization: any inverse-polynomial ϵ_num > 0, time n^{O_k(1)} → any positive rational ϵ_num in binary, time polynomial in the input length (degree depending on k); reason: for ϵ_num = 1/poly(n) the input length is n^{O(k)} (τ alone has n bits) and ϵ_num has O(log n) bits, so this specializes to the source
--   - encoding: a rational point of the relaxation (10)–(14) → a rational moment list satisfying SDPFeasible k n r for the shifted instance; reason: the paper's own parametrization (proof of Lemma 4.7, p.20)
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.7, p.20

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_RelaxFeasible
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

/-- **Lemma 4.7 (Exactly feasible near-optimal points).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.7, p.20: "For n ≥ k ≥ 3, k ≤ r ≤ n, and
any inverse-polynomial ϵ_num > 0, an exactly feasible rational point of the relaxation (10)–(14)
with L ≤ OPT_{τ,r} + ϵ_num can be computed in n^{O_k(1)} bit time."

For every `k ≥ 3`, a polynomial-time map from `(I, τ, r, ϵ_num)` to a rational moment list that is
exactly feasible for (10)–(14) of the shifted instance and has objective `≤ OPT_{τ,r} + ϵ_num`.

**Formalization Note.** §4's setting (p.15): arbitrary well-formed `k`-uniform instance with at most
one predicate per scope, coordinates XORed with `τ` (`shift`). `ϵ_num` is any positive rational in
binary (this covers every inverse-polynomial `ϵ_num`, whose bit length is `O(log n)`), and the time
is polynomial in the input length, `n^{O_k(1)}` for such `ϵ_num`. Feasibility includes `Z ⪰ 0`
(Mathlib's `Matrix.PosSemidef` of the real matrix). -/
theorem lemma_4_7 (k : ℕ) (hk : 3 ≤ k) :
    ∃ solve : GInst × List Bool × ℕ × ℚ → List (List ℕ × ℚ),
      Nonempty (Turing.TM2ComputableInPolyTime encSDPIn encMom solve) ∧
      ∀ I : GInst, I.WellFormed → I.Uniform k → I.ScopeUnique → k ≤ I.n →
        ∀ τ : Fin I.n → Bool, ∀ r : ℕ, k ≤ r → r ≤ I.n → ∀ ε : ℚ, 0 < ε →
          SDPFeasible k I.n r (solve (I, List.ofFn τ, r, ε)) ∧
          relaxObj (shift I τ) (solve (I, List.ofFn τ, r, ε)) ≤ (OPTball I τ r : ℚ) + ε := by sorry

end AcceptSubcube
