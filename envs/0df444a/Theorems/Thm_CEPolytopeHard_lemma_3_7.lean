-- Prove2me | Theorems.Thm_CEPolytopeHard_lemma_3_7
-- name    : CEPolytopeHard.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:06.346979+00:00
-- url     : https://prove2.me/theorems/553cc212-b9fc-42a8-8a42-7e4d9fd30c6a
-- title:
--   Lemma 3.7 — the average entropy $h(t)$ is nonincreasing
-- statement:
--   Let $P$ be a stochastic $k \times k$ matrix with stationary distribution $\mu$, and for $0 < t \le 1$ let $P(t) = t(I - (1-t)P)^{-1}$ and $h(t) = \mathbb E_{i\sim\mu} H(P_i(t))$ (entropy with natural logarithms). Then for $0 < t \le s \le 1$,
--   $$
--   h(s) \le h(t),
--   $$
--   i.e. $h$ is nonincreasing on $(0, 1]$.
--
--   Since $h$ takes values in $[0, \log k]$, among $r$ scales $1 = t_0 > t_1 > \dots > t_r$ some consecutive pair has $h(t_\ell) - h(t_{\ell-1}) \le \log k / r$; this logarithmic dependence on the support size $k$ is what Section 3.2 needs.
--
--   Differences from the source:
--   - encoding: P(t) = E_{a∼Geo(t)} P^a; "h is nonincreasing" → the printed closed form t(I − (1 − t)P)⁻¹; ∀ 0 < t ≤ s ≤ 1, h(s) ≤ h(t); reason: the closed form equals the series for 0 < t ≤ 1; monotonicity on the domain (0, 1] of h
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Lemma 3.7, p.15 (definitions of P(t), h(t) on the same page)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_CEPolytopeHard_hEnt

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Lemma 3.7 (the average entropy is nonincreasing)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 3.2, p.15: "For a parameter
0 < t ≤ 1, we define P(t) := E_{a∼Geo(t)} P^a = t ∑_{a=0}^∞ (1 − t)^a P^a = t(I − (1 − t)P)^{−1},
h(t) := E_{i∼μ} H(P_i(t)) where H is entropy with natural logarithms and P(1) = I. Lemma 3.7. h is
nonincreasing").

For every stochastic `k × k` matrix `P` with stationary distribution `μ`, and
`0 < t ≤ s ≤ 1`, `h(s) ≤ h(t)`.

**Formalization Note** The setting of Section 3.2 (a transition matrix of a fixed set with its
stationary distribution) enters only through `P` stochastic and `μ` stationary. -/
theorem lemma_3_7 {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (hP : IsStochastic P) (μ : Fin k → ℝ)
    (hμ : IsStationary P μ) (t s : ℝ) (ht : 0 < t) (hts : t ≤ s) (hs : s ≤ 1) :
    hEnt P μ s ≤ hEnt P μ t := by sorry

end CEPolytopeHard
