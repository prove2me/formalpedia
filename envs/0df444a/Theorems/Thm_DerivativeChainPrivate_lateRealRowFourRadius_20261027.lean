-- Prove2me | Theorems.Thm_DerivativeChainPrivate_lateRealRowFourRadius_20261027
-- name    : DerivativeChainPrivate.lateRealRowFourRadius_20261027
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:07:47.472445+00:00
-- url     : https://prove2.me/theorems/52369a47-5b78-4335-89a2-100cf6862b06
-- title:
--   Four radii from a real-rooted row within fifteen derivatives
-- statement:
--   Let a degree-n complex polynomial have all source roots, counted with multiplicity, in the closed disk of center c and radius R, with R nonnegative. Write n=M+K+1 and assume K is at most fifteen. Suppose its actual degree-(M+1) derivative row has only real roots, with multiplicity; equivalently, that row is a nonzero scalar times the product of the linear factors corresponding to a sorted real list b.
--
--   Then there is a complete actual derivative-root chain z, choosing one root in every nonconstant ordinary derivative row, whose total Euclidean length is at most 4R.
--
--   The intermediate real row is an explicit algebraic hypothesis. The theorem supplies the entire chain, with no assumed short prefix or turning budget. It is a restricted class theorem, not the unrestricted four-radius conjecture.
-- source:
--   Private project Amal-David/derivative-chain-prize, formal/late-real-row/lean/LateRealRowActual.lean, theorem exists_chain_cost_le_four_of_late_real_row; exact SHA-256 294c856a512ec8b27220ef9268fd6669af641494fb08dcd2e10ff649c4eefea0; independently reviewed in formal/late-real-row/INDEPENDENT_REVIEW.md. Analytic provenance: commit c8843d6c870e743f53f8920ecc20d4d7a3505fcf, research-results/new-structures/coherent-selection-20261024/RESULT.md Section 2(B).

import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
open scoped BigOperators
set_option autoImplicit false

theorem DerivativeChainPrivate.lateRealRowFourRadius_20261027 {n : ℕ} (a : Fin n → ℂ)
    (M K : ℕ) (hn : n=M+K+1) (hK : K≤15) (c : ℂ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ i, ‖a i-c‖≤R) (b : Fin (M+1) → ℝ) (hb : Monotone b)
    (s : ℂ) (hs : s≠0)
    (hcore : row a (M+1)=C s*∏ i, (X-C (b i : ℂ))) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z≤4*R := by sorry
