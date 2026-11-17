-- Prove2me | Theorems.Thm_AddXnor_Supplement_theorem_4
-- name    : AddXnor.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:32:40.847455+00:00
-- url     : https://prove2.me/theorems/708736c7-eba9-47d7-b1eb-63aa564c2c2b
-- title:
--   Theorem 4 — Exact average correlation
-- statement:
--   For every $N\ge2$ and $m\ge2$, the signed correlation averaged uniformly over all $N-1$ operator bits is exactly
--   $$
--   \mathbb E_{x\leftarrow\{0,1\}^{N-1}}[\operatorname{Cor}(x)]=(N+1)2^{-N}.
--   $$
--
--   The average is signed; no absolute value or planted distribution is involved.
--
--   Differences from the source:
--   - encoding: uniform operator string $x\in\{0,1\}^{N-1}$ → exact finite average over `Fin (N-1) → Bool`; reason: finite-type encoding with identical uniform weights
-- source:
--   Wang, Lv, Shen, Zhang, manuscript (sha256 405d6dda…), Theorem 4, p.16 (PDF p.16)

import Mathlib
import Definitions.Def_AddXnor_Supplement_core

set_option autoImplicit false

namespace AddXnor.Supplement

/-- **Theorem 4 (Exact average correlation)** (Wang, Lv, Shen, Zhang,
*Add/XNOR Chains*, manuscript, sha256 405d6dda..., Theorem 4, p.16 (PDF p.16)).

This is the signed average of `Cor(x)`, not the average absolute correlation. -/
theorem theorem_4 (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m) :
    uniformMean (fun x : Fin (N - 1) → Bool => correlation (m := m) x) =
      (N + 1 : ℝ) * Real.rpow 2 (-(N : ℝ)) := by sorry

end AddXnor.Supplement
