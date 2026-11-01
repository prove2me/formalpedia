-- Prove2me | Theorems.Thm_ColumnRandLP_step_3_EC_13
-- name    : ColumnRandLP.step_3_EC_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:50.398577+00:00
-- url     : https://prove2.me/theorems/55673a96-e6f8-4b02-b975-57d9da98e152
-- title:
--   (EC.9)–(EC.13) — if $P_J$ is feasible and $p$ is dual optimal, $v(P_J)\le v(P_{\mathrm{distr}})+\|x'-x^{*0}\|_2+\|p\|_\infty\|b'-b\|_1$
-- statement:
--   Let $A$ be an $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$ with $\|c\|_2=1$, $\xi$ a probability distribution on $[n]$, $C$ a constant, and $x^{*0}$ an optimal solution of $P_{\mathrm{distr}}:\min\{c^Tx\mid Ax=b,\ 0\le x\le C\xi\}$. Fix a sample $J=(j_1,\dots,j_K)$, $K\ge1$, and let $x'=\frac1K\sum_k\frac{x^{*0}_{j_k}}{\xi_{j_k}}e_{j_k}$ and $b'=Ax'$. If the column-randomized problem $P_J$ is feasible and $p$ is any optimal solution of its dual $D_J:\max\{p^Tb\mid p^TA_J\le c_J^T\}$, then
--   $$
--   v(P_J)\le v(P_{\mathrm{distr}})+\|x'-x^{*0}\|_2+\|p\|_\infty\cdot\|b'-b\|_1 .
--   $$
--
--   This is the deterministic Step 3 of the proof of Proposition EC.3: it turns the two probabilistic bounds (EC.5) and (EC.7) into a bound on the optimal value of $P_J$, using Lemma EC.3, the Cauchy–Schwarz and Hölder inequalities and $\|c\|_2=1$.
--
--   **Formalization Note** $v(P_J)$ and $v(P_{\mathrm{distr}})$ are real infima; $P_J$ is feasible by hypothesis and bounded below because $D_J$ has an optimal solution, and $P_{\mathrm{distr}}$ has the optimal solution $x^{*0}$. $\|c\|_2=1$ is $\sum_j c_j^2=1$.
--
--   Differences from the source:
--   - generalization: the standing assumptions of §3.1 that P is feasible and bounded and rank(A) = m → not assumed; reason: Step 3 does not involve v(P) or rank(A); the statement specializes to the paper's setting
--   - encoding: v(P_J), v(P_distr) → real infima vJ, vDistr; reason: P_J is feasible by hypothesis and bounded below by weak duality with p, and P_distr attains its minimum at x*⁰, so both infima are the paper's minima
--   - reading: K, the number of samples → 1 ≤ K; reason: x′ averages K terms
--   - generalization: a sample J drawn from ξ, so that every ξ_{j_k} > 0 and x′ is defined → every J : Fin K → Fin n (ordered, repeats allowed), with Lean's x / 0 = 0 at ξ_{j_k} = 0; reason: such a J has probability 0, and x0_j = 0 there, so the term vanishes; the statement specializes to the paper's samples
--   - encoding: C a nonnegative constant (Proposition EC.3) → no separate hypothesis; reason: x0 feasible for P_distr and ∑ ξ_j = 1 force C ≥ 0
--   - encoding: ‖p‖∞ = max_i |p_i| → supNorm p = ⨆ i, |p i|; reason: a supremum over a finite nonempty index type is the maximum; at m = 0, where the max is undefined, it is 0
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, proof of Proposition EC.3, Step 3, (EC.8)–(EC.13), p.ec9

import Mathlib
import Definitions.Def_ColumnRandLP_StandardLP
import Definitions.Def_ColumnRandLP_Norms
import Definitions.Def_ColumnRandLP_Model

open Matrix

namespace ColumnRandLP

/-- **Step 3 of the proof of Proposition EC.3, (EC.9)–(EC.13)** (Akchen–Mišić,
arXiv:2007.10461v5, proof of Proposition EC.3, Step 3, (EC.9)–(EC.13), p.ec9). Let `x*⁰` be an
optimal solution of `P_distr`, `J` a sample, `x′ = (1/K) ∑_k (x*⁰_{j_k}/ξ_{j_k}) e_{j_k}` and
`b′ = A x′`. If the column-randomized problem `P_J` is feasible and `p` is any optimal solution of
its dual `D_J : max {pᵀb | pᵀA_J ≤ c_Jᵀ}`, then
`v(P_J) ≤ v(P_distr) + ‖x′ − x*⁰‖₂ + ‖p‖∞ · ‖b′ − b‖₁` (using `‖c‖₂ = 1`).

**Formalization Note** Deterministic, for one sample `J : Fin K → Fin n` (repeats allowed).
`v(P_J) = vJ A b c J`, `v(P_distr) = vDistr A b c C ξ` (real infima; `P_J` is feasible by
hypothesis and bounded below because its dual has the optimal solution `p`; `P_distr` has the
optimal solution `x0`). `‖c‖₂ = 1` is `∑ c_j² = 1`. The other standing assumptions on `P`
(feasible, bounded, `rank A = m`) are not needed for this step and are not assumed. -/
theorem step_3_EC_13 {m n K : ℕ} (hK : 1 ≤ K) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hc : ∑ j, c j ^ 2 = 1) (ξ : Fin n → ℝ)
    (hξ0 : ∀ j, 0 ≤ ξ j) (hξ1 : ∑ j, ξ j = 1) (C : ℝ) (x0 : Fin n → ℝ)
    (hx0 : IsDistrOptimal A b c C ξ x0) (J : Fin K → Fin n)
    (hJ : IsFeasible (sampleMat A J) b) (p : Fin m → ℝ)
    (hp : IsDualOptimal (sampleMat A J) b (sampleCost c J) p) :
    vJ A b c J ≤ vDistr A b c C ξ + l2Norm (xprime ξ x0 J - x0) +
      supNorm p * l1Norm (A *ᵥ xprime ξ x0 J - b) := by sorry

end ColumnRandLP
