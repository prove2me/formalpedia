-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_approx_bad_inclusions
-- name    : DenseProdQSAT.Testing.approx_bad_inclusions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:31.500082+00:00
-- url     : https://prove2.me/theorems/55498310-0f52-4119-bbbb-1f20ff6b7eff
-- title:
--   §4.2.3, Eq. (11) — comparison of exact and approximate bad sets
-- statement:
--   Let $n,d\ge1$, $k\ge2$, $0<\varepsilon\le1$, and let $\Phi$ be an instance. Fix support-associated collections of common positive length $L$ whose potentials satisfy Lemma 4.11's absolute accuracy bound on every local assignment of size at most $4e^d/\tau_J+1$. For a local assignment $A$ of size at most $4e^d/\tau_J$ and every $1\le i\le J$,
--
--   $$R_i(A)\subseteq\widetilde R_i(A)\subseteq R_{i+1}(A).$$
--
--   Each bad set uses all prefix times and compatible unit vectors, and the approximate drop uses the collections for the two separate supports. These inclusions connect the range-space sampling conclusion with the original bad sets.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), §4.2.3, Eq. (11), p. 16

import Definitions.Def_DenseProdQSAT_Testing_Approximation
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem approx_bad_inclusions {n k d L : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hL : 1 ≤ L) (Φ : Instance n k d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Q : CollectionFamily n k L) (hQ : AccurateFamily Φ ε Q)
    (F : List (Fin n)) (ψ : States n d) (hA : IsLocal Φ F ψ)
    (hF : (F.length : ℝ) ≤ 4 * Real.exp d / Tau (ScaleCount ε))
    (i : ℕ) (hi : i ∈ Finset.Icc 1 (ScaleCount ε)) :
    BadSet Φ F ψ i ⊆ ApproxBadSet Φ Q F ψ i ∧
      ApproxBadSet Φ Q F ψ i ⊆ BadSet Φ F ψ (i + 1) := by sorry

end DenseProdQSAT.Testing
