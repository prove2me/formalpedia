-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_eq_13
-- name    : EntanglingOps.BinaryPhase.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:27.285087+00:00
-- url     : https://prove2.me/theorems/d0f72523-76d3-4c02-82b1-c966fe7bca44
-- title:
--   Eq. (13), p. 3 (corrected: 5.97931 < f_∞ < 5.97932) — f_N < f_∞, the series for f_∞ converges
-- statement:
--   Let $E(\psi_{\alpha_k})$ be the entropy of entanglement of the resource state for $\alpha_k=\pi/2^k$, and
--   $$f_N=\frac1\pi\sum_{k=1}^N2^kE(\psi_{\alpha_k}),\qquad f_\infty=\frac1\pi\sum_{k=1}^\infty2^kE(\psi_{\alpha_k}).$$
--   Then:
--
--   1. the series $\sum_{k\ge1}2^kE(\psi_{\alpha_k})$ converges;
--   2. $f_N<f_\infty$ for every $N$;
--   3. $$5.97931<f_\infty<5.97932.$$
--
--   The paper prints $f_\infty=5.97932$. Together with Eq. (12), this gives $\bar E[U(\alpha_N)]<\alpha_Nf_\infty<5.97932\,\alpha_N$: the entanglement cost of $U(\alpha_N)$ is at most a fixed multiple of the phase.
--
--   Differences from the source:
--   - correction: f_∞ = 5.97932 → 5.97931 < f_∞ < 5.97932; reason: f_∞ = (1/π) Σ_{k≥1} 2^k h(cos²(π/2^k)) = 5.9793137464654… (40-digit evaluation), which is 5.97931 to the printed five decimals; the printed inequality f_N < 5.97932 remains true
--   - generalization: f_N < f_∞ for the paper's N ≥ 1 → for every N : ℕ (f_0 = 0); reason: N ≥ 1 is an instance
--   - encoding: f_∞ as an infinite sum → (1/π)·tsum over k : ℕ of 2^{k+1} E(ψ_{α_{k+1}}), with summability asserted; reason: Lean's tsum is 0 on a non-summable series; asserting Summable makes f_∞ the genuine sum
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, Eq. (13)

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

/-- Eq. (13), p. 3 (corrected value): the series `∑_{k≥1} 2^k E(ψ_{α_k})` converges,
`f_N < f_∞` for every `N`, and `5.97931 < f_∞ < 5.97932` (the paper prints `f_∞ = 5.97932`; the
value is `5.9793137…`). -/
theorem eq_13 :
    Summable (fun k : ℕ => (2 : ℝ) ^ (k + 1) * entEntropy (resource (alphaN (k + 1)))) ∧
    (∀ N : ℕ, fN N < fInf) ∧ (5.97931 : ℝ) < fInf ∧ fInf < 5.97932 := by sorry

end EntanglingOps.BinaryPhase
