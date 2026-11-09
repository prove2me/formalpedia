-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_proposition_16
-- name    : ChvatalOneHard398.SAT.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:33.812158+00:00
-- url     : https://prove2.me/theorems/49be52b8-99b9-4cb5-99c8-078273d47529
-- title:
--   Proposition 16 — the formulas F(p,h,H,D,t)
-- statement:
--   Let $m,m'\ge1$, $D\ge2$, $h\ge1$, and let $p_1,\ldots,p_s\ge2$ be pairwise coprime with $\Pi=\prod_jp_j\ge2^h$ and $p_{\max}=\max_jp_j$. Let $H\in\{0,\ldots,D-1\}^{m'\times m}$, $t\in\mathbb Z^m$, $M=\Lambda_D^\perp(H)$, and $d=Ht\bmod D$.
--   The concrete formula $F=F(p,h,H,D,t)$ is computable in the stated polynomial time and has nonempty clauses of at most three literals. Writing $B_h=\{-(2^{h-1}-1),\ldots,2^{h-1}\}^m$, it satisfies
--
--   $$\operatorname{SAT}(F)\simeq\{\widetilde y\in M:t-\widetilde y\in B_h\}.$$
--
--   If $\lambda_1(M)>m^{3/2}p_{\max}(2^h-1)/2$, every rational subpolyhedron of $P(F)$ has Chvátal rank at most one, and $F$ has at most one satisfying assignment. Finally $F$ has at most $2m\sum_jp_j+66C$ variables, where $C=6m(\sum_jp_j)(\lfloor\log_2\Pi\rfloor+2)+6m'mh(\lfloor\log_2D\rfloor+2)$. This packages all three conclusions of the proposition for the construction used by the reduction.
--
--   Differences from the source:
--   - encoding: time polynomial in m,m′,Σp,log D and the encoding size of t → unary m,m′,p,h and binary D,H,t as encParams; reason: h≤log₂Π≤Σp on valid parameters, so input length is polynomially equivalent to the printed numerical parameters
--   - encoding: deterministic polynomial time in structured bit size → TM2 polynomial time with fixed, dimension-prefixed, length-framed binary encodings; reason: these encodings are injective and have length linear in the corresponding bit size
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
--   - encoding: finite families of nonempty literal sets → lists of finite literal sets with explicit range and nonemptiness checks; reason: repeated clauses are harmless and repeated literals must not be counted
--   - encoding: O(m(Σp)log Π+m′mh log D) variables → at most 2mΣp+66C variables, with C the explicit gate bound; reason: p.26 gives at most 10 variables, 54 row-literal occurrences and 2 fixings per gate; free variables and their multiple-choice rows contribute 2mΣp
--   - encoding: the formula of Lemma 18 applied to X with shifted target → latticeFormula uses exactly t+(2^(h-1)−1)·1 before the exact-one conversion; reason: this is the actual construction on p.25, including the asymmetric box convention
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.18, Proposition 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT

theorem proposition_16 :
    PolyTime encParams encFormula latticeFormula ∧
    ∀ a : Params, a.Valid →
      (latticeFormula a).WellFormed ∧
      (∀ T ∈ (latticeFormula a).clauses, T.card ≤ 3) ∧
      Nonempty (assignments (latticeFormula a) ≃ candidateVectors a) ∧
      (IsThin a → hereditaryRankOne (satPolytope (latticeFormula a)) ∧
        Subsingleton (assignments (latticeFormula a))) ∧
      (latticeFormula a).N ≤ formulaBound a := by sorry

end ChvatalOneHard398.SAT
