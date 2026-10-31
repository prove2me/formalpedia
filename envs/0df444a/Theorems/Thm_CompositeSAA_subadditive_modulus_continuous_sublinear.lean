-- Prove2me | Theorems.Thm_CompositeSAA_subadditive_modulus_continuous_sublinear
-- name    : CompositeSAA.subadditive_modulus_continuous_sublinear
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:29.282735+00:00
-- url     : https://prove2.me/theorems/45af30e3-ce1e-4575-b286-e648ce667d2d
-- title:
--   Proof of Theorem 4, p.7 — a subadditive modulus is continuous with sublinear growth (corrected: nondecreasing)
-- statement:
--   Let $w$ be a modulus of continuity ($w\ge0$ on $[0,\infty)$, $\lim_{t\downarrow0}w(t)=w(0)=0$) that is nondecreasing and subadditive on $[0,\infty)$. Then $w$ is continuous on $[0,\infty)$, and there are positive constants $\alpha,\beta$ with
--
--   $$
--   w(t)\le\alpha t+\beta\qquad\text{for all } t\ge0 .
--   $$
--
--   Combined with the previous step it gives every function of the class $\tilde{\mathfrak F}$ the bound $|g(x)|\le\alpha\|x\|+b$, which makes the class uniformly integrable when first moments converge.
--
--   Differences from the source:
--   - correction: "Any subadditive modulus of continuity is continuous" → a nondecreasing subadditive modulus; reason: $w(t)=t$ on $[0,1]$ and $w(t)=\tfrac12$ for $t>1$ is a subadditive modulus of continuity that is discontinuous at $1$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 4, p.7

import Mathlib
import Definitions.Def_CompositeSAA_IsModulus

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 4, p.7 (corrected): a
nondecreasing subadditive modulus of continuity `w` is continuous on `[0, ∞)` and has sublinear
growth: there are positive constants `α`, `β` with `w(t) ≤ α t + β` for all `t ≥ 0`.

**Formalization Note** Correction: the printed claim ("Any subadditive modulus of continuity is
continuous") omits "nondecreasing" and is false without it: `w(t) = t` on `[0, 1]`, `w(t) = 1/2`
for `t > 1` is a subadditive modulus, discontinuous at `1`. -/
theorem subadditive_modulus_continuous_sublinear (w : ℝ → ℝ) (hw : IsModulus w)
    (hmono : MonotoneOn w (Set.Ici 0))
    (hsub : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → w (s + t) ≤ w s + w t) :
    ContinuousOn w (Set.Ici 0) ∧
      ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ t : ℝ, 0 ≤ t → w t ≤ α * t + β := by sorry

end CompositeSAA
