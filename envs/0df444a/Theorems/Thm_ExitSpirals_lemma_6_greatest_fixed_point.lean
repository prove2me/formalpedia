-- Prove2me | Theorems.Thm_ExitSpirals_lemma_6_greatest_fixed_point
-- name    : ExitSpirals.lemma_6_greatest_fixed_point
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:02.490601+00:00
-- url     : https://prove2.me/theorems/65ce5eaa-83e4-45f3-9776-dd6f6376d7de
-- title:
--   Lemma 6, fixed-point part (corrected: in-degree system, C1; the activity clause is in the Lemmas 3 and 6 bounds) — $s^*(x)$ is the greatest fixed point and gives the greatest solution of (9)
-- statement:
--   Let $p_R,p_C$ be joint degree distributions and $x\in[0,1]$. Let $g_R,g_C$ be the corrected giant-component fractions and $F(s,x)=x\,g_R(x\,g_C(s))$. Then
--
--   1. $s^*(x)=\sup\{s\in[0,1]: s\le F(s,x)\}$ is the greatest $s\in[0,1]$ with $F(s,x)=s$;
--   2. the pair $\big(s^*(x),\ x\,g_C(s^*(x))\big)$ is the coordinatewise greatest solution $(s_R,s_C)\in[0,1]^2$ of
--   $$s_R=x\,g_R(s_C),\qquad s_C=x\,g_C(s_R),$$
--   which is the system (9) with $f_R,f_C$ eliminated.
--
--   So the sizes $s^*_R,s^*_C$ of Lemma 6 are well defined, by Tarski's fixed point theorem, as the greatest solution.
--
--   **Formalization Note** $f_\mu$ is fixed as the smallest root of $f=H_\mu(1-s+sf)$ (`extinctionProb`), and $\sum_{jk}\hat p_{jk}(s)f^j$ is written as $G(1-s+sf)$ by binomial thinning (8).
--
--   Differences from the source:
--   - correction: (9) and Lemma 5: g(f) = 1 − Σ_jk p_jk f^k with H built from p⁺_k = Σ_j (j/λ) p_jk (out-links) → g(s) = 1 − G(1 − s + s f(s)), G(z) = Σ_jk p_jk z^j, f the smallest root of f = H(1 − s + s f) with H built from p⁻_j = Σ_k (k/λ) p_jk (p.46); reason: the printed formula measures who can reach the giant component, but stability needs support from it: with in-degree 2 for all agents and out-degree 0 or 4 with probability ½ (Assumption 4.5 holds), every agent is active at x = 1 by Lemma 2, while the printed g gives ½ − ½f⁴ < ½
--   - correction: Lemma 6: 'activity is then Â(x) := s* = x g_R(x g_C(s*))' → not stated in this item; the corrected activity a(x) = s* g_C(s*) is the subject of lemmas_3_6_upper and lemmas_3_6_lower; reason: s* counts agents unshocked with support through R only; activity also needs support through C. In the (2,2)-regular case at x = 0.95, s* = 0.94703 while activity is 0.94406 (simulation with n = 200000: 0.9438, 0.9441)
--   - generalization: under the assumptions of §4 (Assumption 4.5, well-behaved tuples) → any two joint degree distributions; reason: Tarski's argument needs only monotonicity of F in s; the source's case is the special case where the laws satisfy Assumption 4.5
--   - encoding: (9) in the unknowns s_R, f_R, s_C, f_C, with p̂_jk(s) of (8) → f_µ = extinctionProb (the smallest root), Σ_jk p̂_jk(s) f^j = G(1 − s + s f); system in (s_R, s_C); reason: f is the smallest root by Lemmas 4 and 8, and binomial thinning (8) gives the generating-function identity
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 6, pp.51–52 (corrected)

import Mathlib
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_giantFrac
import Definitions.Def_ExitSpirals_coupledMap

namespace ExitSpirals

/-- **Lemma 6, corrected, fixed-point part: `s*(x)` is the greatest fixed point of `F(·, x)` and
gives the greatest solution of the system (9).**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 6, p.51:
"the size of the giant out-component in the R (C) network s*_R (s*_C) is the greatest solution
to (9)", and p.52: "the expression x g_R(x g_C(s*)) is monotonically increasing in s … Then by
Tarski's fixed point theorem a maximum fixed point s* exists."

For joint degree distributions `p_R`, `p_C` and `x ∈ [0, 1]`:
1. `s*(x) = sup {s ∈ [0,1] : s ≤ F(s, x)}` is the greatest `s ∈ [0, 1]` with `F(s, x) = s`;
2. `(s*(x), x g_C(s*(x)))` is the coordinatewise greatest solution `(s_R, s_C) ∈ [0,1]²` of
   `s_R = x g_R(s_C)`, `s_C = x g_C(s_R)` (the system (9) with `f_µ` eliminated).

**Formalization Note.** `g_µ = giantFrac p_µ` is the corrected `g` of (9) (in-degree convention;
`f_µ` is its smallest root `extinctionProb`). -/
theorem lemma_6_greatest_fixed_point (pR pC : ℕ → ℕ → ℝ) (hpR : IsDegreeDist pR)
    (hpC : IsDegreeDist pC) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ coupledMap pR pC s x = s} (sStar pR pC x) ∧
      IsGreatest {q : ℝ × ℝ | q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
          q.1 = x * giantFrac pR q.2 ∧ q.2 = x * giantFrac pC q.1}
        (sStar pR pC x, x * giantFrac pC (sStar pR pC x)) := by sorry

end ExitSpirals
