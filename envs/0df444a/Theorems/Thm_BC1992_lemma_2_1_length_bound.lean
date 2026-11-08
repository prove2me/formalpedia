-- Prove2me | Theorems.Thm_BC1992_lemma_2_1_length_bound
-- name    : BC1992.lemma_2_1_length_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-08T00:36:33.580543+00:00
-- url     : https://prove2.me/theorems/c4159d87-6398-4832-a778-db34d2e08579
-- title:
--   Lemma 2.1: Syntactic Polynomial Max-Output-Length Bound for Bellantoni-Cook Programs
-- statement:
--   Proves monotonicity of syntactic polynomials `Poly` and Lemma 2.1 of Bellantoni and Cook (1992): for every Bellantoni-Cook program $f : \mathsf{Fn}\;n\;m$, normal arguments $\vec{x}$ with $\forall x \in \vec{x},\; |x| \le N$, and safe arguments $\vec{y}$,
--
--   $$|f(\vec{x}; \vec{y})| \le q_f(N) + \max_{y \in \vec{y}} |y|,$$
--
--   where $q_f = f.\mathsf{sizePoly} : \mathsf{Poly}$ is synthesized by structural recursion on $f$, together with specializations to purely normal programs ($f : \mathsf{Fn}\;n\;0$), unary programs ($f : \mathsf{Fn}\;1\;0$), and uniform normal-and-safe length bounds ($f.\mathsf{fullSizePoly}$).
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Section 2, Lemma 2.1, pp. 100-101.

import Definitions.Def_BC1992_Syntax

namespace BC1992

/-- **Lemma 2.1 (Bellantoni & Cook 1992 — Syntactic Polynomial Output-Length Bound)**:
    1. Every syntactic polynomial `p : Poly` is monotone on `Nat`.
    2. For every `f : Fn n m`, normal inputs `xs` with `∀ x ∈ xs, x.length ≤ N`, and safe inputs `ys`,
       `(f.eval xs ys).length ≤ f.sizePoly.eval N + Fn.maxLen ys`.
    3. When `f : Fn n 0` has no safe inputs (`ys = []`), `(f.eval xs []).length ≤ f.sizePoly.eval N`.
    4. For a unary program `f : Fn 1 0` and input word `x : Word`,
       `(f.eval [x] []).length ≤ f.sizePoly.eval x.length`.
    5. When all normal inputs `xs` and safe inputs `ys` have length at most `K`,
       `(f.eval xs ys).length ≤ f.fullSizePoly.eval K`. -/
theorem lemma_2_1_length_bound :
    (∀ (p : Poly) {n m : Nat}, n ≤ m → p.eval n ≤ p.eval m) ∧
    (∀ {n m : Nat} (f : Fn n m) (xs ys : List Word) {N : Nat},
      (∀ x ∈ xs, x.length ≤ N) →
      (f.eval xs ys).length ≤ f.sizePoly.eval N + Fn.maxLen ys) ∧
    (∀ {n : Nat} (f : Fn n 0) (xs : List Word) {N : Nat},
      (∀ x ∈ xs, x.length ≤ N) →
      (f.eval xs []).length ≤ f.sizePoly.eval N) ∧
    (∀ (f : Fn 1 0) (x : Word),
      (f.eval [x] []).length ≤ f.sizePoly.eval x.length) ∧
    (∀ {n m : Nat} (f : Fn n m) (xs ys : List Word) {K : Nat},
      (∀ x ∈ xs, x.length ≤ K) →
      (∀ y ∈ ys, y.length ≤ K) →
      (f.eval xs ys).length ≤ f.fullSizePoly.eval K) := by
  sorry

end BC1992
