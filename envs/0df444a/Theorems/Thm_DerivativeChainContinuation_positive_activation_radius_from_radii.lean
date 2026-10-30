-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_activation_radius_from_radii
-- name    : DerivativeChainContinuation.positive_activation_radius_from_radii
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:24:54.066475+00:00
-- url     : https://prove2.me/theorems/c27f5313-e571-4812-ae78-409af5034570
-- title:
--   Activation radius equals the power sum of the positive source radii
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. Let k≥2, r,d∈ℕ and positive real numbers ρ_0,…,ρ_d be given, with repetitions allowed. Suppose the actual source is p_a=X^r∏_(j=0)^d(X^k-ρ_j^k). Then every actual derivative chain z satisfies |z_(k-1)|=((Σ_(j=0)^dρ_j^k)/choose(N,k))^(1/k).
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveRayCorollaries.lean, lines 346-362, SHA-256 7174fbbd4d36931f506b63017e7bd24da0afc12d26638665a78878a7c892072f.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_activation_radius_from_radii (n d : ℕ) (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (ρ : Fin (d+1) → ℝ) (hk : 2 ≤ k) (hρ : ∀ j,0<ρ j)
    (hp : fromRoots a=spokePoly k r (realRootProduct (fun j => (ρ j)^k)))
    (hz : DerivativeChainPrivate.IsChain a z) :
    ‖complexHistoryOf z (k-1)‖=((∑ j,(ρ j)^k)/(Nat.choose (n+1) k : ℝ))^((k : ℝ)⁻¹) := by sorry
