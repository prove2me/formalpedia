-- Prove2me | Theorems.Thm_BipColorHard_lemma_30
-- name    : BipColorHard.lemma_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:28.867083+00:00
-- url     : https://prove2.me/theorems/2526136f-20b6-48b9-b203-8004d7deabbf
-- title:
--   Lemma 30 — two types: uniqueness, and multiplicities $(k,k+1)$ win
-- statement:
--   Let $q=2k+1\ge5$, $d=q$. Fix a partition $[q]=I\cup J$ into nonempty sets of sizes $s,t$, and maximize $\Phi$ over pairs of probability vectors constant on $I$ and on $J$. Let $V(s)$ be the maximum. Then:
--
--   1. there are exactly two maximizing pairs $(P,R)$ and $(R,P)$; both are positive stationary pairs of $\Phi$, and $P\ne R$;
--   2. $V(s)=V(q-s)$;
--   3. $V(1)<\dots<V(k)$.
--
--   So among two-type pairs, the multiplicities $(k,k+1)$ are the optimal ones, which is what yields a phase for each $k$-subset.
--
--   Differences from the source:
--   - encoding: the value $V(s)$, depending only on $s$ → `twoTypeV` indexed by $I$, equal for sets of equal size and of complementary sizes; reason: the dependence only on $s$ is the manuscript's remark before the lemma, and it is stated here
--   - encoding: maximum of $\Phi$ over the constant pairs → pairs with $P^{\mathsf T}BR>0$; reason: $\Phi$ is defined there; other pairs have value $-\infty$
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 30, p.34 (PDF p.36)

import Definitions.Def_BipColorHard_Objective

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 30**, p.34 (PDF p.36), manuscript sha256 78a66d1f…. Range of §7: `q = 2k + 1 ≥ 5`, `d = q`. Fix a partition
`[q] = I ∪ Iᶜ` into nonempty sets, normalize each vector to have coordinate sum one, and consider the pairs for which
both vectors are constant on `I` and on `Iᶜ`. There are exactly two maximizing pairs of `Φ`, `(P, R)` and `(R, P)`; both
are positive stationary pairs of `Φ`, and `P ≠ R`. Moreover `V(s) = V(q - s)` and `V(1) < ⋯ < V(k)`.

**Formalization Note.** `V` is indexed by the set `I`; the first clause on `V` says it depends only on `s = |I|` (the
manuscript's permutation remark) and that `V(s) = V(q - s)`, and the second is the strict monotonicity. -/
theorem lemma_30 (k : ℕ) (hk : 2 ≤ k) :
    (∀ I : Finset (Fin (2 * k + 1)), I.Nonempty → Iᶜ.Nonempty →
      ∃ P R : Fin (2 * k + 1) → ℝ, P ≠ R ∧
        IsStationary (2 * k + 1) P R ∧ IsStationary (2 * k + 1) R P ∧
        ∀ P' R', IsTwoTypeMax (2 * k + 1) I P' R' ↔ (P' = P ∧ R' = R) ∨ (P' = R ∧ R' = P)) ∧
    (∀ I J : Finset (Fin (2 * k + 1)), I.Nonempty → Iᶜ.Nonempty → J.Nonempty → Jᶜ.Nonempty →
      (J.card = I.card ∨ J.card + I.card = 2 * k + 1) →
        twoTypeV (2 * k + 1) I = twoTypeV (2 * k + 1) J) ∧
    (∀ I J : Finset (Fin (2 * k + 1)), I.Nonempty → I.card < J.card → J.card ≤ k →
      twoTypeV (2 * k + 1) I < twoTypeV (2 * k + 1) J) := by sorry

end BipColorHard
