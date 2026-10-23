-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_16
-- name    : FairRentFPTAS.Approx.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:04.95054+00:00
-- url     : https://prove2.me/theorems/e74dd3f1-6dfb-4138-ae6f-e16c5c6ff0eb
-- title:
--   Lemma 16, p. 37 — quasilinear envy-free allocations are exactly the maximum-weight perfect matchings
-- statement:
--   Let $B=(B^a_r)_{a,r\in[n]}$ be real base values and consider quasilinear utilities $v_a(r,x)=B^a_r-x$. For an allocation (permutation) $\pi$ of $[n]$, there is a rent vector $p\in\mathbb R^n$ such that $(\pi,p)$ is envy-free if and only if $\pi$ is a maximum-weight perfect matching of the complete bipartite graph with edge weights $B^a_r$:
--   $$\Big(\exists p\ \forall a,r:\ B^a_r-p_r\le B^a_{\pi(a)}-p_{\pi(a)}\Big)\iff\forall\sigma:\ \sum_a B^a_{\sigma(a)}\le\sum_a B^a_{\pi(a)}.$$
--
--   This is the characterization behind Step 2 of Algorithm 1 (an envy-free starting point for the quasilinear tail of $\hat{\mathcal I}$) and behind Lemma 18.
--
--   **Formalization Note** Rents may have any sign.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 37, Appendix A, Lemma 16

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 16, p. 37: with quasilinear utilities `v_a(r, x) = B^a_r − x`, an allocation `π`
can be supported by envy-free prices (of any sign) iff it is a maximum-weight perfect matching of
the complete bipartite graph with weights `B^a_r`. -/
theorem lemma_16 {n : ℕ} (B : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    (∃ p : Fin n → ℝ, ∀ a r, B a r - p r ≤ B a (π a) - p (π a)) ↔
      ∀ σ : Equiv.Perm (Fin n), ∑ a, B a (σ a) ≤ ∑ a, B a (π a) := by sorry

end FairRentFPTAS.Approx
