-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_claim_4_5
-- name    : BourgainUnion.Euclidean.claim_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:02.593235+00:00
-- url     : https://prove2.me/theorems/1337fe4d-10c7-4cbf-9a56-856d67303800
-- title:
--   Claim 4.5 — reversible matrix exponential estimate
-- statement:
--   Let $G$ be a finite undirected graph with nonnegative symmetric weights $w_{bb'}$ and zero diagonal, let $L$ be its nonnormalized Laplacian, and assign positive real weights $s_b$ to all vertices. Put $C=\operatorname{diag}(s)$, $K=C^{-1}L$, and $P(t)=\exp(-tK)$. For every $t\ge0$, all entries of $P(t)$ are nonnegative and
--   $$P(t)\mathbf1=\mathbf1,\qquad CP(t)=P(t)^TC,\qquad P(t)^Ts=s.$$
--   For vectors $z_b$ in any real Hilbert space,
--   $$\sum_{b,b'}s_bP_{bb'}(t)\|z_b-z_{b'}\|^2\le2t\sum_{b<b'}w_{bb'}\|z_b-z_{b'}\|^2.$$
--   The left sum is ordered and the right sum counts each unordered pair once. No connectivity assumption is imposed. This is the semigroup estimate used when a Euclidean set is eliminated.
--
--   Differences from the source:
--   - encoding: a graph on a subset and a sum over unordered pairs → a weight matrix supported on that subset, with half the ordered-pair energy sum; reason: the zero diagonal and symmetry give exactly the same energy, including disconnected and all-zero graphs
--   - encoding: P(t)1=1 and P(t)^T s=s → the corresponding coordinate sum identities; reason: these are exactly the same matrix-vector equations; the reversibility equation remains a matrix equality
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 16, Claim 4.5, equation (8)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Claim 4.5: the actual matrix exponential, all identities, and the ordered-pair estimate. -/
theorem claim_4_5 {B : Type*} [Fintype B] [DecidableEq B]
    (G : ClusterDecomp.WGraph B) (hG : Loopless G) (s : B → ℝ) (hs : ∀ b, 0 < s b)
    (t : ℝ) (ht : 0 ≤ t) :
    (∀ b c, 0 ≤ heatMatrix G.w s t b c) ∧
    (∀ b, ∑ c, heatMatrix G.w s t b c = 1) ∧
    Matrix.diagonal s * heatMatrix G.w s t =
      (heatMatrix G.w s t).transpose * Matrix.diagonal s ∧
    (∀ b, ∑ c, heatMatrix G.w s t c b * s c = s b) ∧
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (z : B → H),
      (∑ b, ∑ c, s b * heatMatrix G.w s t b c * ‖z b - z c‖^2) ≤
        2*t*((1/2)*∑ b, ∑ c, G.w b c * ‖z b - z c‖^2)) := by sorry

end BourgainUnion.Euclidean
