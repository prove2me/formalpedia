-- Prove2me | Theorems.Thm_ColumnRandLP_lemma_EC_3
-- name    : ColumnRandLP.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:12.279463+00:00
-- url     : https://prove2.me/theorems/cb1e2f6c-2ae6-4b5e-9c99-b5a57c7ee739
-- title:
--   Lemma EC.3 — right-hand-side sensitivity $z(b)-z(b')\le p^T(b-b')$ for an optimal dual solution $p$
-- statement:
--   Let $A_0$ be an $m\times N$ matrix and $c_0\in\mathbb R^N$, and for $b,b'\in\mathbb R^m$ let
--   $$
--   z(b)=\min\{c_0^Ty\mid A_0y=b,\ y\ge0\},\qquad z(b')=\min\{c_0^Ty\mid A_0y=b',\ y\ge0\}.
--   $$
--   If $p$ is an optimal dual solution of the former problem, i.e. $p^TA_0\le c_0^T$ and $p$ maximizes $q^Tb$ over all $q$ with $q^TA_0\le c_0^T$, then
--   $$
--   z(b)-z(b')\le p^T(b-b').
--   $$
--
--   This is the standard sensitivity fact that an optimal dual solution is a subgradient of the optimal value as a function of the right-hand side; the paper uses it to compare $P_J$ with the problem whose right-hand side is $b'=Ax'$.
--
--   **Formalization Note** $z(\cdot)$ is the real infimum `lpValue`. The existence of an optimal dual solution already makes $z(b)$ finite. The second problem is assumed feasible: when it is infeasible, $z(b')=+\infty$ and the inequality holds trivially. No rank condition on $A_0$ is imposed.
--
--   Differences from the source:
--   - encoding: z(b′) may be +∞ → the second problem is assumed feasible; reason: when it is infeasible the paper's inequality reads z(b) − ∞ ≤ pᵀ(b − b′) and holds trivially, while Lean's sInf ∅ = 0 would not represent +∞
--   - encoding: min, optimal dual solution → real infimum lpValue, IsDualOptimal (dual feasible and attaining the dual maximum); reason: the dual optimum makes both infima finite and attained, so they are the minima
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, Lemma EC.3, p.ec7

import Mathlib
import Definitions.Def_ColumnRandLP_StandardLP

open Matrix

namespace ColumnRandLP

/-- **Lemma EC.3** (Akchen–Mišić, arXiv:2007.10461v5, Lemma EC.3, p.ec7). Let
`z(b) = min {c₀ᵀy | A₀y = b, y ≥ 0}` and `z(b′) = min {c₀ᵀy | A₀y = b′, y ≥ 0}`. Then
`z(b) − z(b′) ≤ pᵀ(b − b′)`, where `p` is an optimal dual solution of the former problem.

**Formalization Note** `z(·)` is `lpValue` (a real infimum). "`p` is an optimal dual solution" is
`IsDualOptimal A₀ b c₀ p`: `pᵀA₀ ≤ c₀ᵀ` and `p` maximizes `qᵀb` over all dual feasible `q`; by LP
duality this already makes `z(b)` finite and attained. The second problem is assumed feasible:
when it is infeasible, `z(b′) = +∞` and the paper's inequality holds trivially (in Lean the `sInf`
of the empty set would be `0`). No rank condition is imposed on `A₀`. -/
theorem lemma_EC_3 {m N : ℕ} (A₀ : Matrix (Fin m) (Fin N) ℝ) (c₀ : Fin N → ℝ)
    (b b' p : Fin m → ℝ) (hp : IsDualOptimal A₀ b c₀ p) (hb' : IsFeasible A₀ b') :
    lpValue A₀ b c₀ - lpValue A₀ b' c₀ ≤ p ⬝ᵥ (b - b') := by sorry

end ColumnRandLP
