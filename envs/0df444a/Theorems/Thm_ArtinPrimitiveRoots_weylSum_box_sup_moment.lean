-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_weylSum_box_sup_moment
-- name    : ArtinPrimitiveRoots.weylSum_box_sup_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T14:51:34.049467+00:00
-- url     : https://prove2.me/theorems/e8cdb834-9892-4c8e-ae7d-ecc84b8caae4
-- title:
--   (3.11) of OpenAI's Prime Predecessors paper — the 2s-th powers of the suprema of the Weyl sum over the boxes of side M^{−j} sum to at most exp(O(sk+k)) M^K J_{s,k}(M)
-- statement:
--   There is a constant $C$ such that for all integers $M, k, s \ge 1$,
--
--   $$\sum_{Q}\ \sup_{\alpha \in Q}|S(\alpha)|^{2s} \le \exp\bigl(C(sk + k)\bigr)\,M^{K}\,J_{s,k}(M),$$
--
--   where $K = k(k+1)/2$, $S$ is the Weyl sum (`weylSum`), $J_{s,k}(M)$ is Vinogradov's count (`vinogradovCount`), and $Q$ runs over the $M^K$ boxes $\prod_{j=1}^{k}[m_j/M^j, (m_j+1)/M^j)$, $0 \le m_j < M^j$, that partition $[0,1)^k$.
--
--   A step toward `log_phase_progression` (Lemma 3.3 of the same paper). The paper proves it by a Sobolev-type bound for the supremum on each box and orthogonality.
--
--   **Formalization note.** The paper's $\exp(O(sk + k))$ is the explicit $\exp(C(sk + k))$ with $C$ absolute. The coordinate `j : Fin k` of `α` corresponds to the paper's $\alpha_{j+1}$, so its box side is $M^{-(j+1)}$.
--
--   OpenAI, *Prime Predecessors with an Even Number of Prime Factors* (2026), p. 7: “Partition the coefficient torus $[0, 1)^k$ into boxes with side length $M^{-j}$ in coordinate $j$. […] We also need the following bound for suprema over boxes $Q$: $\sum_Q \sup_{\alpha \in Q}|S(\alpha)|^{2s} \le \exp(O(sk + k))M^KJ_{s,k}(M)$. (3.11)”
-- source:
--   OpenAI, Prime Predecessors with an Even Number of Prime Factors, OpenAI Math Release preprint, September 17, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf (Apache-2.0), p. 7, proof of Lemma 3.3, (3.11)

import Mathlib
import Definitions.Def_ArtinVinogradov

namespace ArtinPrimitiveRoots

open Real

theorem weylSum_box_sup_moment :
    ∃ C : ℝ, ∀ M k s : ℕ, 1 ≤ M → 1 ≤ k → 1 ≤ s →
      ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
          (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
              α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
            ‖weylSum M k α.1‖ ^ (2 * s)) ≤
        exp (C * ((s : ℝ) * k + k)) * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ) := by
  sorry

end ArtinPrimitiveRoots
