-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_theorem_B_3
-- name    : BirthdayEntropy.Soundness.Supplement.theorem_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:15.732329+00:00
-- url     : https://prove2.me/theorems/2cd69be2-faa3-4a20-b2d8-9593288b219d
-- title:
--   Theorem B.3 — Ternary compatibility graph soundness
-- statement:
--   Let $\Phi$ be any indexed Boolean CSP on $n$ variables with arbitrary predicates on exactly three distinct variables per constraint. Suppose every global assignment $g$ has a family of at least $\gamma n$ violated constraints with pairwise disjoint scopes; this family may depend on $g$. Assume $0<\gamma\le1/3$, $n\ge16/\gamma$, and $2\le\ell\le\sqrt n$. Let $K=\binom n\ell$. For every set $H$ of exactly $K$ distinct vertices of the published compatibility graph $G_{\Phi,\ell}$,
--
--   $$\operatorname{density}_{\Phi}(H)\le1-\frac{\gamma^2\ell^3}{13600n^2}.$$
--
--   Density counts unordered distinct edges. The quantification includes missing views, multiple different answers on one view, and locally invalid isolated vertices. There is no bounded-occurrence, nonisolation, CNF or base-gap assumption. This companion additive soundness theorem is not used in the proof of Theorem 2.1.
--
--   Differences from the source:
--   - encoding: 2 <= ell <= sqrt(n) → natural-number ell with 2 <= ell and ell^2 <= n; reason: these conditions are equivalent on nonnegative integers
--   - encoding: a set of K distinct Boolean labelled views → a Finset of published Vertex (Fin n coordinates) with card = choose n ell; reason: finite sets enforce distinctness and represent every source selection; normalization is unchanged
--   - encoding: a Boolean ternary CSP with assignment-dependent disjoint violations → published indexed CSP and forall g exists J of pairwise disjoint violated indices; reason: repeated scopes, arbitrary predicates and isolated variables remain allowed
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Theorem B.3, PDF p24-25 / printed p23-24

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Exposure

namespace BirthdayEntropy.Soundness.Supplement

/-- Theorem B.3, PDF pp24–25 / printed pp23–24. Companion theorem; not
used in the proof of the goal. No nonisolation, degree, gap or CNF assumption. -/
theorem theorem_B_3 (n m ℓ : ℕ) (φ : CSP n m) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1/3) (hn : 16 / γ ≤ (n : ℝ))
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ^2 ≤ n) (hφ : DisjointViolationPromise φ γ)
    (H : Finset (Vertex n ℓ)) (hH : H.card = Nat.choose n ℓ) :
    density φ H ≤ 1 - γ^2 * (ℓ : ℝ)^3 / (13600 * (n : ℝ)^2) := by sorry

end BirthdayEntropy.Soundness.Supplement
