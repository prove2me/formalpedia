-- Prove2me | Theorems.Thm_BalancedKneser_theorem_11_1
-- name    : BalancedKneser.theorem_11_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:36.811951+00:00
-- url     : https://prove2.me/theorems/40b4f1a2-1f7e-4b94-82bd-0b7abdb07b74
-- title:
--   Theorem 11.1 — integral-to-fractional injectivity $H_j(C_2(N,k))\to H_j(Y_2)$ for $j\le7$
-- statement:
--   Let $1\le k<N$, let $C=C_2(N,k)$ be the complex of families of $k$-subsets of $[N]$ with a common integral center at Johnson distance at most two, and let $Y=Y_2$ be the complex of families with a common fractional radius-two center, so that $C\subseteq Y$ with inclusion $i$. Suppose that
--   $$
--   \tilde H_t\big(C_2(9,3);\mathbb Z\big)=\tilde H_t\big(C_2(8,4);\mathbb Z\big)=0\qquad(0\le t\le7).\tag{11.1}
--   $$
--   Then for both coefficient rings $\mathbb k=\mathbb Z$ and $\mathbb k=\mathbb F_2$, the induced map
--   $$
--   i_*:\ H_j(C;\mathbb k)\longrightarrow H_j(Y;\mathbb k)
--   $$
--   is injective for $0\le j\le 7$.
--
--   With Propositions B.5 and C.8 (which establish (11.1)), this is what makes the radius-two generators of Proposition 4.1 available, and hence the ten-color bound.
--
--   **Formalization Note** Homology is singular homology of realizations, and $i_*$ is induced by the inclusion $|C_2(N,k)|\subseteq|Y_2|$. Hypothesis (11.1) is kept as a hypothesis, in the encoding of the vanishing predicate (path-connected, and $H_t=0$ for $1\le t\le7$).
--
--   Differences from the source:
--   - encoding: hypothesis (11.1): H̃_t(C₂(9, 3); ℤ) = H̃_t(C₂(8, 4); ℤ) = 0 (0 ≤ t ≤ 7) → IsReducedAcyclicThrough ℤ (realization (CC 2 9 3)) 7 ∧ IsReducedAcyclicThrough ℤ (realization (CC 2 8 4)) 7; reason: for nonempty complexes H̃₀ = 0 means connected and H̃_t = H_t for t ≥ 1; both complexes are nonempty
--   - encoding: simplicial homology of the complex → singular homology of its geometric realization (Hatcher.Singular.H); reason: the two agree for finite simplicial complexes; same groups
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Theorem 11.1, p.27 (PDF p.29); proof §11.1–11.5, pp.28–33

import Mathlib
import Definitions.Def_Hatcher_SingularHomology
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_inclusionMap
import Definitions.Def_BalancedKneser_CC
import Definitions.Def_BalancedKneser_Yfrac
import Definitions.Def_BalancedKneser_IsReducedAcyclicThrough

namespace BalancedKneser

/-- **Theorem 11.1** (Alipour–Jafari, arXiv:2611.04486v1, p.27 (PDF p.29); proof §11.1–11.5):
"Suppose that H̃_t(C2(9, 3); Z) = H̃_t(C2(8, 4); Z) = 0 (0 ≤ t ≤ 7). (11.1) Then
i_* : H_j(C; k) → H_j(Y; k) is injective for 0 ≤ j ≤ 7."

Standing hypotheses of §11 (p.27): `1 ≤ k < N`, `C = C₂(N, k)`, `Y = Y₂`, and coefficients
`k = ℤ` or `F₂` (both are asserted). `i : C ↪ Y` is the inclusion (an integral center is a
fractional one). Hypothesis (11.1) is kept as a hypothesis, in the encoding of
`IsReducedAcyclicThrough`.

Formalization Note: homology is singular homology of realizations; `i_*` is induced by the
inclusion `|C₂(N, k)| ⊆ |Y₂|`. -/
theorem theorem_11_1 (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N)
    (h11 : IsReducedAcyclicThrough ℤ (TreeCoverLB.realization (CC 2 9 3)) 7 ∧
      IsReducedAcyclicThrough ℤ (TreeCoverLB.realization (CC 2 8 4)) 7) :
    ∀ j ≤ 7,
      Function.Injective (Hatcher.Singular.map ℤ j (inclusionMap (CC_subset_Yfrac 2 N k))).hom ∧
      Function.Injective
        (Hatcher.Singular.map (ZMod 2) j (inclusionMap (CC_subset_Yfrac 2 N k))).hom := by sorry

end BalancedKneser
