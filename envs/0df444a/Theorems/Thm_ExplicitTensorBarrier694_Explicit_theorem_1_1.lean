-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_theorem_1_1
-- name    : ExplicitTensorBarrier694.Explicit.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:16.210929+00:00
-- url     : https://prove2.me/theorems/af837010-1fef-4ac8-ae4e-a9925821a3be
-- title:
--   Theorem 1.1 — polynomial-time explicit integer tensors of border rank at least $3n-11n^{3/4}$
-- statement:
--   There is a single family of integer tensors $F_n\in\mathbb Z^{n\times n\times n}$ that is polynomial-time explicit and whose complex border rank satisfies, for every positive integer $n$,
--
--   $$\underline R(F_n)\ge3n-11n^{3/4}.$$
--
--   Polynomial-time explicit means one fixed finite-state deterministic machine takes $n$ in binary and prints all $n^3$ entries in binary in at most $C(n+1)^d$ steps for fixed integers $C\ge1,d\ge0$. The output is linked to exactly the same family appearing in the border-rank bound. Border rank is over $\mathbb C$, with unrestricted complex approximating tensors.
--
--   The definition layer supplies the paper's intended zero-padded block witness from Theorem 3.5 for $n\ge16$ and the zero choice for smaller positive dimensions. The goal itself retains the source's existential family claim, and assumes neither witness conciseness nor runtime nor restriction lower bounds. This is a paper-proved result awaiting a formal proof, not an open conjecture.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional complex mode spaces → coordinate spaces with arbitrary natural dimensions; reason: choosing bases identifies every source instance with one of these arrays; tensors, dual subspaces, and Koszul maps are transported by those bases
--   - encoding: least rank in a complex limit → least r whose rank-at-most-r locus has the tensor in its topological closure; reason: finite complex product spaces are metrizable, so sequential limits and closure agree; approximants remain arbitrary complex tensors
--   - encoding: a deterministic algorithm records all integer entries in binary in time polynomial in n → one finite-state Mathlib TM0 machine with signed delimited binary lexicographic output and actual step bound C(n+1)^d; reason: fixed finite alphabet, one tape, sign and delimiter conventions admit polynomial simulation and represent the same explicit families; constants and machine precede every positive dimension
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Theorem 1.1, p.2, equation (1.1) and its following explicitness paragraph; detailed witness Theorem 3.5, p.11 (PDF pp.2,11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Explicitness

namespace ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Theorem 1.1, p.2 (1.1),
including the immediately following definition of polynomial-time explicitness.
Theorem 3.5, p.11, supplies explicitFamily as a witness for n≥16; zero handles
smaller positive n. No runtime, conciseness, or restriction-rank hypothesis.
Both clauses concern the SAME integer family, uniform over every positive n. -/
theorem theorem_1_1 :
    ∃ F : (n : ℕ) → Fin n → Fin n → Fin n → ℤ,
      PolynomialTimeExplicit F ∧ ∀ n : ℕ, 0 < n →
        3 * (n : ℝ) - 11 * (n : ℝ) ^ ((3 : ℝ) / 4) ≤
          (borderRank (complexify (F n)) : ℝ) := by sorry

end ExplicitTensorBarrier694.Explicit
