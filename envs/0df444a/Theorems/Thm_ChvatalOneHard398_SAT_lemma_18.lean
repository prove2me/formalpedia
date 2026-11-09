-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_18
-- name    : ChvatalOneHard398.SAT.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:27.90654+00:00
-- url     : https://prove2.me/theorems/e6df554e-ba44-49ef-9423-20e5dd8ecebb
-- title:
--   Lemma 18 — exact-one systems as three-literal formulas
-- statement:
--   Let $T$ be a finite family of nonempty literal sets on $N$ variables. The concrete chain-and-clause construction produces a well-formed formula $F$ in time polynomial in $N+\sum_{C\in T}|C|$, with
--
--   $$N(F)\le N+\sum_{C\in T}|C|,\qquad |C|\le3\ (C\in F),\qquad\operatorname{SAT}(F)\simeq X(T)\cap\mathbb Z^N.$$
--
--   If every rational subpolyhedron of $X(T)$ has Chvátal rank at most one, the same holds for every rational subpolyhedron of $P(F)$. This transfers exact-one formulations to the target formula class.
--
--   Differences from the source:
--   - encoding: finite families of nonempty literal sets → lists of finite literal sets with explicit range and nonemptiness checks; reason: repeated clauses are harmless and repeated literals must not be counted
--   - encoding: deterministic polynomial time in structured bit size → TM2 polynomial time with fixed, dimension-prefixed, length-framed binary encodings; reason: these encodings are injective and have length linear in the corresponding bit size
--   - encoding: the numerical complexity parameter N+Σ|T| → N in unary in encExactInput; reason: binary N alone could encode an arbitrarily large unused variable count too briefly
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.19, Lemma 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT

theorem lemma_18 :
    PolyTime encExactInput encFormula exactToSAT ∧
    ∀ T : Formula, T.WellFormed →
      (exactToSAT T).WellFormed ∧ (exactToSAT T).N ≤ T.N + literalCount T ∧
      (∀ C ∈ (exactToSAT T).clauses, C.card ≤ 3) ∧
      Nonempty (assignments (exactToSAT T) ≃ integralPoints (exactOne T)) ∧
      (hereditaryRankOne (exactOne T) → hereditaryRankOne (satPolytope (exactToSAT T))) := by sorry

end ChvatalOneHard398.SAT
