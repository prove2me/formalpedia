-- Prove2me | Theorems.Thm_BSPConvex_CMM_lifted_set_convex
-- name    : BSPConvex.CMM.lifted_set_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:43.874986+00:00
-- url     : https://prove2.me/theorems/7bb10acf-d9f5-47cc-af6a-60c35737a700
-- title:
--   Proof of Theorem 2, p. 28 — the set {(q, Z) | T(q)^{1/2} ⪰ Z, q ∈ Δm} is convex
-- statement:
--   Let $\Sigma\succeq 0$. The set
--   $$\big\{(q,Z)\in\mathbb R^m\times\mathbb R^{m\times m} : T(q)^{1/2}\succeq Z,\ q\in\Delta_m\big\}$$
--   is convex.
--
--   This is the last step of the proof of Theorem 2: together with the convexity of the other two epigraph constraints it shows that the epigraph of $g$ is convex.
--
--   **Formalization Note** $T(q)^{1/2}\succeq Z$ is `(CFC.sqrt (T q) - Z).PosSemidef`, so membership forces $Z$ symmetric. The paper's $\Sigma$ is a covariance matrix; only positive semidefiniteness is assumed.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 28, proof of Theorem 2

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem lifted_set_convex {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef) :
    Convex ℝ {p : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ |
      (CFC.sqrt (Tmat Sig p.1) - p.2).PosSemidef ∧ p.1 ∈ simplex m} := by sorry

end BSPConvex.CMM
