-- Prove2me | Theorems.Thm_AdditiveConvexity_lemma_EC_1
-- name    : AdditiveConvexity.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:12.53219+00:00
-- url     : https://prove2.me/theorems/ae565932-b1a9-4fed-bd03-3033aaea7afc
-- title:
--   Lemma EC.1 (Karush): the minimum over an interval splits into its two ends
-- statement:
--   Let $A\subseteq B$ be convex subsets of $\mathbb R$ such that every point of $B$ lies above a point of $A$, and let $\varphi$ be convex on $A$. Then:
--
--   1. there are $G$ convex and increasing on $A$ and $H$ convex and decreasing on $B$ with
--   $$
--   \min_{\theta\in A\cap[a,b]}\varphi(\theta)=G(a)+H(b)
--   $$
--   for all $a\in A$, $b\in B$, $a\le b$ at which the minimum exists;
--   2. for every minimizer $S\in A$ of $\varphi$ on $A$, clause 1 holds with $G(a)=\varphi(\max\{S,a\})-\varphi(S)$ and $H(b)=\varphi(\min\{S,b\})$, and then the minimum exists for every such pair.
--
--   This classical result, stated without proof in the paper, is the step that passes additive convexity through one minimization.
--
--   **Formalization Note** No attainment hypothesis is made: the printed $\min$ is read as presupposing existence pair by pair.
--
--   Differences from the source:
--   - generalization: x and y both in the convex set I → left end in A, right end in a convex superset B of A whose points each lie above a point of A; reason: (EC.2) applies the lemma with y = y₁, which may lie above I; B = A is the printed lemma
--   - reading: `min_{x≤θ≤y} f(θ)`, with no existence claim → for each pair a ≤ b, every v with `IsLeast (φ '' (A ∩ Icc a b)) v` equals G a + H b; no attainment hypothesis; reason: on I = [0, 1] the convex function with f(0) = 1, f(t) = t for t > 0 has no minimum on [0, 1], so the printed min presupposes existence, pair by pair
--   - generalization: "in particular" clause gives the formulas for g and h → also asserts that, with these formulas, the minimum over A ∩ [a, b] exists and is G a + H b for every pair; reason: given a minimizer S the minimum is attained at S, a or b, so the printed clause is the special case
--   - reading: `h(x) = f(min{S, y})` → H b = φ (min S b); reason: the printed h(x) is a typo for h(y)
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Lemma EC.1, p.ec1 (PDF p.18)

import Mathlib
import Definitions.Def_AdditiveConvexity_IsKarushDecomposition

namespace AdditiveConvexity

/-- **Lemma EC.1** (Karush's lemma). Gong–Wang, Preservation of Additive Convexity, SSRN 3217007
(accepted manuscript), Lemma EC.1, p.ec1 (PDF p.18). Let `φ` be convex on the convex set `A`, and
let `B ⊇ A` be a convex set each of whose points lies above a point of `A`. Then `φ` has a Karush
decomposition `G`, `H`: for all `a ∈ A`, `b ∈ B` with `a ≤ b`, any minimum of `φ` on `A ∩ [a, b]`
is `G a + H b`. For every minimizer `S` of `φ` on `A`, one is `G a = φ (max S a) - φ S`,
`H b = φ (min S b)`, and with it the minimum on `A ∩ [a, b]` exists for every such pair.

**Formalization Note.** `B = A` is the printed lemma. The printed `min` is not assumed to exist:
the identity is asserted for each pair whose minimum exists, and no attainment hypothesis is
made. The printed "`h(x) = f(min{S, y})`" is read as `h(y)`. -/
theorem lemma_EC_1 {A B : Set ℝ} {φ : ℝ → ℝ} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAB : A ⊆ B)
    (hBA : ∀ b ∈ B, ∃ a ∈ A, a ≤ b) (hφ : ConvexOn ℝ A φ) :
    (∃ G H : ℝ → ℝ, IsKarushDecomposition A B φ G H) ∧
      ∀ S ∈ A, (∀ a ∈ A, φ S ≤ φ a) →
        IsKarushDecomposition A B φ (fun a => φ (max S a) - φ S) (fun b => φ (min S b)) ∧
          ∀ a ∈ A, ∀ b ∈ B, a ≤ b →
            IsLeast (φ '' (A ∩ Set.Icc a b)) (φ (max S a) - φ S + φ (min S b)) := by sorry

end AdditiveConvexity
