-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_lemma9
-- name    : DirectedHamiltonicity.Main.lemma9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:57.606802+00:00
-- url     : https://prove2.me/theorems/8f397903-21b8-4593-aa40-4635f20e439d
-- title:
--   Lemma 9 — a fixed $X\in\mathcal X(R)$ is sampled with probability $\prod_i(2-2^{-d_i})^{-1}\ge(2-2^{-d})^{-(n-2)}$
-- statement:
--   Let $H$ be a normalized weighted directed multigraph on $n$ vertices (no loops, no arc entering $s$, no arc leaving $t$, parallel arcs of distinct weights), $s\ne t$, in which the arcs entering each vertex have at most $d\ge1$ distinct weights. Fix $R=(R_i)_{i\in I}$ with $R_i\subseteq W_i$. For each $i\in I$ choose $a_i$ independently and uniformly from $\mathbb F_2^{d_i+1}\setminus\{0\}$, where $d_i=|W_i|$. Then for every $X\in\mathcal X(R)$,
--   $$\Pr_a\bigl[X\in\mathcal X_a(R)\bigr]=\prod_{i\in I}\bigl(2-2^{-d_i}\bigr)^{-1}\ \ge\ \bigl(2-2^{-d}\bigr)^{-(n-2)}.$$
--   Both the equality and the inequality are asserted.
--
--   Each set that survives the determinant test is found by one random linear system with probability only exponentially smaller than $1$ by the factor $(2-2^{-d})^{-(n-2)}$, which sets the number of systems the algorithm of Proposition 4 must try.
--
--   Differences from the source:
--   - encoding: probability over independent uniform choices → the number of tuples a ∈ ∏_i (F₂^{Option W_i} ∖ {0}) with X ∈ 𝒳_a(R), divided by the number of all such tuples; reason: the uniform product law on a finite set, written as a ratio of cardinalities
--   - encoding: 2^{−d_i}, 2^{−d}, and (2 − 2^{−d})^{−(n−2)} → (1/2)^{d_i}, (1/2)^d and ((2 − (1/2)^d)^{n−2})⁻¹ with n = |V| (natural subtraction; n ≥ 2 since s ≠ t, and n − 2 = |I|); reason: equal real numbers
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.10 / printed p.9, Lemma 9 (Equation (1) and setting PDF pp.9–10 / printed pp.8–9)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum

namespace DirectedHamiltonicity.Main

open Multidigraph

open Classical in
/-- Lemma 9, PDF p.10 / printed p.9. Let `H` be a normalized weighted multigraph (no loops, no arc
entering `s`, no arc leaving `t`, parallel arcs of distinct weights) on `n` vertices, `s ≠ t`, in which
the arcs entering each vertex have at most `d ≥ 1` distinct weights, and fix `R = (R_i)_{i ∈ I}`,
`R_i ⊆ W_i`. For each `i ∈ I` choose `a_i` independently and uniformly from `𝔽₂^{d_i+1} ∖ {0}`
(`d_i = |W_i|`). Then for every `X ∈ 𝒳(R)`,
`Pr_a[X ∈ 𝒳_a(R)] = ∏_{i ∈ I} (2 − 2^{−d_i})^{−1} ≥ (2 − 2^{−d})^{−(n−2)}`. -/
theorem lemma9 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (hnorm : H.IsNormalized w s t)
    (d : ℕ) (hd : 1 ≤ d) (hdeg : ∀ v, (H.incomingWeights w v).card ≤ d)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (X : Finset (Internal s t)) (hX : X ∈ H.survivors w s t R) :
    ((Finset.univ.filter fun a : H.NonzeroCoeffs w s t =>
          X ∈ H.sampled w s t (fun i => (a i).1) R).card : ℝ) /
        (Fintype.card (H.NonzeroCoeffs w s t) : ℝ) =
      ∏ i : Internal s t, (2 - (1 / 2 : ℝ) ^ (H.incomingWeights w i.1).card)⁻¹ ∧
    ((2 - (1 / 2 : ℝ) ^ d) ^ (Fintype.card V - 2))⁻¹ ≤
      ∏ i : Internal s t, (2 - (1 / 2 : ℝ) ^ (H.incomingWeights w i.1).card)⁻¹ := by sorry

end DirectedHamiltonicity.Main
