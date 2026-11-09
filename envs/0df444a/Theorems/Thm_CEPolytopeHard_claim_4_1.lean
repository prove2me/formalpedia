-- Prove2me | Theorems.Thm_CEPolytopeHard_claim_4_1
-- name    : CEPolytopeHard.claim_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:16:42.884496+00:00
-- url     : https://prove2.me/theorems/7f582de5-5914-4752-aaf1-b8dacf5411dc
-- title:
--   Claim 4.1 — properties of the Bernstein approximation
-- statement:
--   Let $h : [0,1]^2 \to [0,1]$ satisfy $|h(a,b) - h(a',b')| \le \lambda(|a - a'| + |b - b'|)$ on $[0,1]^2$, and let $p \ge 1$ be an integer. Let $f$ be the Bernstein approximation of $h$ of degree $p$. Then
--
--   1. $f$ is a polynomial of degree at most $p$ in each input: $f(a,b) = \sum_{u,v \le p} c_{uv} a^u b^v$ (so of total degree at most $2p$);
--   2. for all $(a, b) \in [0,1]^2$,
--   $$
--   0 \le f(a,b) \le 1, \qquad |f(a,b) - h(a,b)| \le \frac{\lambda}{\sqrt p}, \qquad |\partial_a f(a,b)|,\ |\partial_b f(a,b)| \le \lambda .
--   $$
--
--   In the proof of Theorem 4 this turns every gate map into a polynomial with controlled error and derivatives.
--
--   Differences from the source:
--   - generalization: f_i, the Bernstein approximation of the gate map h_i of p.20, with a constant λ ≥ 1 → the Bernstein approximation of any h : [0, 1]² → [0, 1] that is λ-Lipschitz in the sum metric, any real λ; reason: the proof uses only the range and the Lipschitz bound; every gate map has both with λ = lam τ
--   - encoding: polynomial of degree at most p in each input; partial derivatives → ∃ coefficients c_uv (u, v ≤ p) with bern p h a b = Σ c_uv a^u b^v for all real a, b; deriv of the one-variable sections; reason: Lean representation of degree and partial derivatives
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Claim 4.1, p.20

import Mathlib
import Definitions.Def_CEPolytopeHard_bern

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Claim 4.1 (properties of the Bernstein approximation)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Claim 4.1, p.20: "For every
integer p ≥ 1, f_i is a polynomial of degree at most p in each input (for a total degree at most
2p). For all (a, b) ∈ [0, 1]², 0 ≤ f_i(a, b) ≤ 1, |f_i(a, b) − h_i(a, b)| ≤ λ/√p,
|∂_a f_i(a, b)|, |∂_b f_i(a, b)| ≤ λ").

For every map `h : [0, 1]² → [0, 1]` with `|h(a, b) − h(a′, b′)| ≤ λ(|a − a′| + |b − b′|)` on
`[0, 1]²` and every integer `p ≥ 1`, the Bernstein approximation `bern p h` is a polynomial
`∑_{u, v ≤ p} c_{uv} a^u b^v`, and on `[0, 1]²` it takes values in `[0, 1]`, is within `λ/√p` of
`h`, and both partial derivatives are at most `λ` in absolute value.

**Formalization Note** The paper states the claim for the gate maps `h_i` of p.20; here `h` is
any map with the two properties the proof uses. -/
theorem claim_4_1 (h : ℝ → ℝ → ℝ) (lam : ℝ)
    (hrange : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, h a b ∈ Set.Icc (0 : ℝ) 1)
    (hlip : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ a' ∈ Set.Icc (0 : ℝ) 1,
      ∀ b' ∈ Set.Icc (0 : ℝ) 1, |h a b - h a' b'| ≤ lam * (|a - a'| + |b - b'|))
    (p : ℕ) (hp : 1 ≤ p) :
    (∃ c : ℕ → ℕ → ℝ, ∀ a b : ℝ, bern p h a b =
      ∑ u ∈ Finset.range (p + 1), ∑ v ∈ Finset.range (p + 1), c u v * a ^ u * b ^ v) ∧
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ bern p h a b ∧ bern p h a b ≤ 1 ∧ |bern p h a b - h a b| ≤ lam / Real.sqrt p ∧
      |deriv (fun a' => bern p h a' b) a| ≤ lam ∧ |deriv (fun b' => bern p h a b') b| ≤ lam := by sorry

end CEPolytopeHard
