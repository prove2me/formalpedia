-- Prove2me | Theorems.Thm_FlowLatRound_proposition_3_7
-- name    : FlowLatRound.proposition_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:48.105198+00:00
-- url     : https://prove2.me/theorems/5e8b6bf9-8239-459a-9a4b-70e4eb20f2b7
-- title:
--   Proposition 3.7 — cycle lengths follow a birthday law: $P(X=\ell)=\frac{(q-2)\,\ell\,(q-1)^\ell(n)_\ell}{(n(q-1))_{\ell+1}}$
-- statement:
--   Draw $(\pi,T)$ from the tilted configuration model of degree $q$ ($q\ge3$, $n\ge2$, $qn$ even), and let $X$ be the length of the fundamental cycle of a uniformly random non-tree edge. Then $X$ has the law of the number of draws, without replacement from $n$ groups of $q-1$ slots each, made before some group is drawn for the second time, and for $1\le\ell\le n$
--   $$P(X=\ell)=\frac{(q-2)\,\ell\,(q-1)^\ell\,(n)_\ell}{(n(q-1))_{\ell+1}}.\tag{7}$$
--
--   Differences from the source:
--   - encoding: X has the law of the birthday waiting time → P(X = ℓ) = P(X′ = ℓ) for every ℓ ∈ ℕ; reason: laws on ℕ are equal iff their point masses are
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Proposition 3.7, Eq. (7), p.9 (PDF 11)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Proposition 3.7, Eq. (7), p.9 (PDF 11). Cycle lengths follow a birthday law: draw
`(π, T)` from the tilted configuration model of degree `q` (`q ≥ 3`, `n ≥ 2`, `qn` even) and let
`X` be the length of the fundamental cycle of a uniformly random non-tree edge. Then `X` has the
law of the number of draws, without replacement from `n` groups of `q − 1` slots each, made
before some group is drawn for the second time, and for `1 ≤ ℓ ≤ n`
`P(X = ℓ) = (q − 2) ℓ (q − 1)^ℓ (n)_ℓ / (n(q − 1))_{ℓ+1}`. -/
theorem proposition_3_7 (q n : ℕ) (hq : 3 ≤ q) (hn : 2 ≤ n) (he : Even (q * n)) :
    (∀ ℓ : ℕ, (regular n q (by omega) he).cycleLenProb ℓ =
      (regular n q (by omega) he).birthdayProb ℓ) ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n →
      (regular n q (by omega) he).cycleLenProb ℓ =
        ((q : ℝ) - 2) * (ℓ : ℝ) * ((q : ℝ) - 1) ^ ℓ * (n.descFactorial ℓ : ℝ) /
          ((n * (q - 1)).descFactorial (ℓ + 1) : ℝ) := by sorry

end FlowLatRound
