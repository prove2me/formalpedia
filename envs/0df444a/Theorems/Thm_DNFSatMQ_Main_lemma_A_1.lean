-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_A_1
-- name    : DNFSatMQ.Main.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:17.337394+00:00
-- url     : https://prove2.me/theorems/34ea2c40-a87a-4a3e-8a9f-d1e3545e49fb
-- title:
--   Lemma A.1 — for an s-term DNF f and g with values in [0,1], E|f − g| ≤ (2s+1)‖f̂ − ĝ‖_∞
-- statement:
--   Let $f:\{0,1\}^d\to\{0,1\}$ be an $s$-term DNF and $g:\{0,1\}^d\to[0,1]$. Then, with expectation over $x\sim U_d$ and $\|\hat f-\hat g\|_\infty = \max_{A\subseteq[d]}|\hat f(A)-\hat g(A)|$,
--   $$\mathbb E\big[|f-g|\big]\le(2s+1)\,\|\hat f-\hat g\|_\infty .$$
--   It turns the Fourier accuracy of the KM algorithm into classification accuracy in the proof of Theorem 8.1.
--
--   Differences from the source:
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: an s-term DNF f → f = φ.eval for a published `SamplingAC0.DNF` φ with φ.length ≤ s; reason: a contradictory term evaluates to false and can be dropped, so the functions are the same
--   - generalization: s ≥ 1 (implicit in "s-term") → every natural s, including s = 0 (f ≡ 0); reason: contains the source's cases
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma A.1, p. 41 (PDF 42)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-- Lemma A.1 (p. 41). Expectations are over `x ∼ U_d`. -/
theorem lemma_A_1 {d s : ℕ} (φ : SamplingAC0.DNF (Fin d)) (hφ : φ.length ≤ s) (g : Pt d → ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    (∑ x : Pt d, |bval (φ.eval x) - g x|) / 2 ^ d ≤
      (2 * s + 1) * supDist (fourierCoeff fun x => bval (φ.eval x)) (fourierCoeff g) := by sorry

end DNFSatMQ.Main
