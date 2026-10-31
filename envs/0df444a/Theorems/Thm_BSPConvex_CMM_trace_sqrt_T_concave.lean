-- Prove2me | Theorems.Thm_BSPConvex_CMM_trace_sqrt_T_concave
-- name    : BSPConvex.CMM.trace_sqrt_T_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:48.143336+00:00
-- url     : https://prove2.me/theorems/c4ebfb2c-2edd-498b-90bb-3d39e8f4da5e
-- title:
--   Proof of Theorem 2, p. 28 — tr(T(q)^{1/2}) is concave in q on Δm
-- statement:
--   Let $\Sigma\succeq 0$. The function
--   $$f(q)=\operatorname{tr}\big(T(q)^{1/2}\big)=\operatorname{tr}\Big(\big(\Sigma^{1/2}S(q)\Sigma^{1/2}\big)^{1/2}\Big)$$
--   is concave on the simplex $\Delta_m$.
--
--   In the proof of Theorem 2 this follows from Lemma 6 and makes the second of the three epigraph constraints, $t+\operatorname{tr}(T(q)^{1/2})\ge z$, a convex constraint.
--
--   **Formalization Note** The paper's $\Sigma$ is a covariance matrix; only positive semidefiniteness is assumed. Only plain concavity is claimed (the paper cites strong concavity of $f$ from Ahipaşaoğlu et al. 2018 elsewhere, which is not stated here). Concavity is Mathlib's `ConcaveOn ℝ Δm f`.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 28, proof of Theorem 2

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem trace_sqrt_T_concave {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef) :
    ConcaveOn ℝ (simplex m) (fCMM Sig) := by sorry

end BSPConvex.CMM
