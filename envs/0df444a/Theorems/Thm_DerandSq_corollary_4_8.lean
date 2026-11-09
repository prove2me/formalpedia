-- Prove2me | Theorems.Thm_DerandSq_corollary_4_8
-- name    : DerandSq.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:11:46.805142+00:00
-- url     : https://prove2.me/theorems/a91da8fd-bea7-4873-a81e-6136a3069a50
-- title:
--   Corollary 4.8 — $\|Q_H(u)\|_{C^*_{\mathrm{red}}(\Gamma_d)} = \Lambda_H$
-- statement:
--   Let $d \geq 3$ and let $H$ be a $k$-regular vertex-transitive graph on $[d]$ with $k \geq 1$. For $s = Q_H(u)$ as in (4.10),
--   $$
--   \|s\|_{C^*_{\mathrm{red}}(\Gamma_d)} = \Lambda_H .
--   $$
--   The limit object of the derandomized square has norm exactly the Cohen–Cohen–Maor–Peled bound; by strong convergence (Theorem 2.14) this is the asymptotic value of $\lambda(G \circledS H)$ for random matching-model graphs.
--
--   Differences from the source:
--   - reading: hypotheses on H implicit (§4 context) → H k-regular and vertex-transitive on Fin d, d ≥ 3, k ≥ 1; reason: the hypotheses of §4 (vertex-transitive H, p.19), the standing assumptions of §4.2, and the proof's use of Theorem 4.7 and vertex-transitivity
--   - encoding: ‖·‖_{C*_red(Γ_d)} → operator norm on ℓ²(Γ_d); reason: C*_red(Γ_d) carries the operator norm
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Corollary 4.8, p.23

import Mathlib
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_DerandSq_LambdaH
import Definitions.Def_DerandSq_QH

namespace DerandSq

/-- Corollary 4.8 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.23. Let `H` be a `k`-regular vertex-transitive graph on `[d]`,
`d ≥ 3`, `k ≥ 1`, and `s = Q_H(u)` as in (4.10). Then `‖s‖_{C*_red(Γ_d)} = Λ_H`.

**Formalization Note** `‖s‖_{C*_red(Γ_d)}` is the operator norm of `QH H` on `ℓ²(Γ_d)`. -/
theorem corollary_4_8 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H) :
    ‖QH H‖ = LambdaH d H := by sorry

end DerandSq
