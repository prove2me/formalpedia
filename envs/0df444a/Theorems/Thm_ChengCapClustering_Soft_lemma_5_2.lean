-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_5_2
-- name    : ChengCapClustering.Soft.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:33.075778+00:00
-- url     : https://prove2.me/theorems/0d761424-1678-4a79-be0b-88a092fe622d
-- title:
--   Lemma 5.2 — certificates extend to vectors: $u,v\ge1$ and $\|p-y\|^z\le u\|p-a\|^z+g\|p-a\|^{z-2}\langle p-a,a-y\rangle+v\|a-y\|^z$
-- statement:
--   Let $z>1$ and let $(u,g,v)$ be a $z$-certificate. Then $u\ge1$, $v\ge1$, and for all $p,a,y\in\mathbb R^d$, $\|p-y\|^z\le u\|p-a\|^z+g\|p-a\|^{z-2}\langle p-a,a-y\rangle+v\|a-y\|^z$, where the middle term is zero if $p=a$.
--
--   Differences from the source:
--   - encoding: "the middle term is zero if p = a" → no separate clause: the middle term is g‖p−a‖^{z−2}⟨p−a, a−y⟩ with Real.rpow; reason: at p = a the inner product is 0, so the Lean term is 0 whatever value 0^{z−2} takes
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 5.2, printed p. 26 / PDF p. 28

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Certificate

namespace ChengCapClustering.Soft

/-- Lemma 5.2 (Certificates extend to vectors), printed p. 26 / PDF p. 28. For `z > 1` and a
`z`-certificate `(u, g, v)`: `u ≥ 1`, `v ≥ 1`, and for all `p, a, y ∈ ℝ^d`,
`‖p − y‖^z ≤ u‖p − a‖^z + g‖p − a‖^{z−2}⟨p − a, a − y⟩ + v‖a − y‖^z` (the middle term is `0` when
`p = a`, since the inner product vanishes). -/
theorem lemma_5_2 (z u g v : ℝ) (hz : 1 < z) (hc : IsCertificate z u g v) :
    1 ≤ u ∧ 1 ≤ v ∧
      ∀ (d : ℕ) (p a y : Euc d),
        ‖p - y‖ ^ z ≤ u * ‖p - a‖ ^ z + g * ‖p - a‖ ^ (z - 2) * inner ℝ (p - a) (a - y) +
          v * ‖a - y‖ ^ z := by sorry

end ChengCapClustering.Soft
