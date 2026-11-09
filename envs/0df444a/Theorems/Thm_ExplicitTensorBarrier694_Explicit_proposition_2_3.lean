-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_proposition_2_3
-- name    : ExplicitTensorBarrier694.Explicit.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:48.60891+00:00
-- url     : https://prove2.me/theorems/7eec42b7-132d-4158-af7b-fa69d8dbbf3a
-- title:
--   Proposition 2.3 — Koszul normalization and border-rank bound
-- statement:
--   Let $a,b,c$ be positive integers and let $0\le p<a$. For the Koszul map on $\mathbb C^a\otimes\mathbb C^b\otimes\mathbb C^c$, both assertions hold:
--
--   $$\rho(K_p)=\binom{a-1}{p},\qquad\forall S,\quad \underline R(S)\ge\frac{\operatorname{rank}K_p(S)}{\binom{a-1}{p}}.$$
--
--   The maximum defining $\rho$ is over pure complex tensors. The denominator is positive on this domain; no equality of mode dimensions is required. The second assertion applies to every complex tensor, including zero. This supplies the Koszul lower bound used in Lemma 3.4.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional complex mode spaces → coordinate spaces with arbitrary natural dimensions; reason: choosing bases identifies every source instance with one of these arrays; tensors, dual subspaces, and Koszul maps are transported by those bases
--   - encoding: least rank in a complex limit → least r whose rank-at-most-r locus has the tensor in its topological closure; reason: finite complex product spaces are metrizable, so sequential limits and closure agree; approximants remain arbitrary complex tensors
--   - encoding: Koszul flattening K_p as an abstract linear map → its matrix in increasing exterior bases z_I and the standard bases of B* and C, with sign (−1)^#{i∈I : i<l} for z_l∧z_I; reason: this is the matrix of the source map in those bases, and rank, kernel dimension and invertibility do not depend on the bases
--   - encoding: ρ(K_p) as a maximum of rank K_p(x⊗y⊗z) over x, y, z → Nat sSup of the set of these ranks; reason: the set is nonempty (zero factors) and bounded by the matrix size, so its sSup is the attained maximum
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Proposition 2.3, p.6 (PDF p.6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Koszul

namespace ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Proposition 2.3, p.6.
Both conclusions, arbitrary nonzero dimensions, every permitted Koszul degree. -/
theorem proposition_2_3 (a b c p : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : p < a) :
    koszulRho a b c p = Nat.choose (a - 1) p ∧
    ∀ S : Tensor a b c,
      ((koszul p S).rank : ℝ) / (Nat.choose (a - 1) p : ℝ) ≤ (borderRank S : ℝ) := by sorry

end ExplicitTensorBarrier694.Explicit
