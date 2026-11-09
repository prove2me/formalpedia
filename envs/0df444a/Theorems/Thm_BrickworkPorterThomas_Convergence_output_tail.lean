-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_output_tail
-- name    : BrickworkPorterThomas.Convergence.output_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:04.895775+00:00
-- url     : https://prove2.me/theorems/a7e4c02a-0e48-48bd-af01-756b98015e29
-- title:
--   Theorem 2.6 — brickwork output probabilities are at most $2k/d$ with probability $1-2^{-k}$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $n\ge2$ be even, $d=2^n$, $k\ge2$, let $l\ge c\,nk$, and fix $b\in\{0,1\}^n$. If $U\sim\mathcal C(l)$ is drawn from the depth-$l$ brickwork Haar random circuit ensemble, then
--
--   $$
--   \Pr_{U\sim\mathcal C(l)}\left[p_U(b)\le\frac{2k}{d}\right]\ge1-2^{-k} .
--   $$
--
--   The output distribution is thus concentrated on the short interval $[0,2k/d]$ with tail mass $\delta=2^{-k}$. This is the concentration hypothesis of Theorem 2.8 in the main proof.
--
--   **Formalization Note** "Depth $l\ge\Omega(nk)$" is read as $l\ge c\,nk$ for one absolute constant $c>0$, fixed before $n,k,l,b$.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: layers numbered 1..l, odd layers on (1,2),(3,4),…, even layers on (2,3),…,(n,1) → layers numbered 0..l−1 with the pairs of the reused brickPair (Lean layer j is the source layer j+1); reason: index shift only; the pairs and the chronological order are the source’s
--   - encoding: depth l ≥ Ω(nk) → ∃ c > 0 (before n, k, l, b) with c n k ≤ l; reason: meaning of the Ω-threshold
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §2, p. 6, Theorem 2.6, Eq. (12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Theorem 2.6 (p. 6). There is an absolute constant `c > 0` such that for brickwork circuits of
depth `l ≥ c n k` on `n = 2M` qubits, `k ≥ 2`, and every fixed `b`, `p_U(b) ≤ 2k/d` with
probability at least `1 − 2^{-k}` over the circuit (`d = 2^n`). -/
theorem output_tail : ∃ c : ℝ, 0 < c ∧
    ∀ (M k l : ℕ) (b : Bits (2 * M)), 1 ≤ M → 2 ≤ k →
      c * ((2 * M : ℕ) : ℝ) * k ≤ l →
      ENNReal.ofReal (1 - (2 : ℝ) ^ (-(k : ℝ))) ≤
        outputLaw M l b (Set.Iic (2 * k / (2 : ℝ) ^ (2 * M))) := by sorry

end BrickworkPorterThomas.Convergence
