-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_lemma10
-- name    : DirectedHamiltonicity.Main.lemma10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:35.351502+00:00
-- url     : https://prove2.me/theorems/1de7b65b-8067-4601-a8fe-7b18f0b820e7
-- title:
--   Lemma 10 — for every fixed $a$, $\mathbb E_R[|\mathcal X_a(R)|]=1$
-- statement:
--   Let $H$ be a normalized weighted directed multigraph (no loops, no arc entering $s$, no arc leaving $t$, parallel arcs of distinct weights), $s\ne t$. For every tuple $a=(a_i)_{i\in I}$ with $a_i\in\mathbb F_2^{d_i+1}\setminus\{0\}$ for each $i\in I$, when the sets $R_i\subseteq W_i$ are chosen independently and uniformly,
--   $$\mathbb E_R\bigl[|\mathcal X_a(R)|\bigr]=1.$$
--
--   The expectation is over $R$ for a fixed $a$, not over $a$, and no rank condition is assumed on the linear system (1). With Markov's inequality this bounds the work of enumerating the solutions of many random systems.
--
--   Differences from the source:
--   - encoding: probability over independent uniform choices → the sum over all R ∈ ∏_i 2^{W_i} of |𝒳_a(R)|, divided by the number of such R; reason: the uniform product law on a finite set, written as a ratio of cardinalities
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.10 / printed p.9, Lemma 10

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum

namespace DirectedHamiltonicity.Main

open Multidigraph

/-- Lemma 10, PDF p.10 / printed p.9. Let `H` be a normalized weighted multigraph (no loops, no arc
entering `s`, no arc leaving `t`, parallel arcs of distinct weights), `s ≠ t`. For every tuple
`a = (a_i)_{i ∈ I}` with `a_i ∈ 𝔽₂^{d_i+1} ∖ {0}`, when the sets `R_i ⊆ W_i` are chosen independently
and uniformly, `E_R[|𝒳_a(R)|] = 1`. -/
theorem lemma10 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hnorm : H.IsNormalized w s t)
    (a : H.NonzeroCoeffs w s t) :
    (∑ R : (i : Internal s t) → Finset (H.incomingWeights w i.1),
        ((H.sampled w s t (fun i => (a i).1) R).card : ℝ)) /
      (Fintype.card ((i : Internal s t) → Finset (H.incomingWeights w i.1)) : ℝ) = 1 := by sorry

end DirectedHamiltonicity.Main
