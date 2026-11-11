-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim16_forward_variance
-- name    : ExpanderWalkDecode.Main.claim16_forward_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:43.446861+00:00
-- url     : https://prove2.me/theorems/d2cd3c64-0a22-4491-97c2-082ad2082983
-- title:
--   Claim 16 — forward variance descent $\tau_{k+1}^2\le\mu_k^2+\lambda^2\tau_k^2$
-- statement:
--   Let $A$ be a locally invertible outer graph with ports $\mathbb F_2^m$ and expansion at most $\lambda^2$, $B$ a Cayley graph on $(\mathbb F_2^m)^s$ ($s\ge1$) with $q\ge1$ generators and expansion at most $\lambda$, where $0<\lambda\le1/4$, and let $\{U_a\}_{a\in A}$ be real symmetric orthogonal $D\times D$ matrices. Let $f_k, M_k(a), M_k, \tau_k^2, \mu_k^2, \Phi_k, g_{r,k}, N_{r,k}(a), N_{r,k}, \sigma^2_{r,k}, \Psi_{r,k}$ be the quantities of Appendix B.6 built from the wide replacement walks of $A$ and $B$ and from $U$.
--   Then for every $0\le k\le t-1$,
--   $$\tau_{k+1}^2\le\mu_k^2+\lambda^2\tau_k^2 .$$
--
--   This is one step of the EML descent used to prove Lemma 4: the variance of the walk average at level $k+1$ is controlled by the conditional mean and the variance at level $k$.
--
--   Differences from the source:
--   - generalization: the construction's graphs: A from Proposition 4 (2^s-regular), B from Proposition 5 on F_2^{s^2} with 2^{s/2} generators, λ = (s²−1)2^{−s/4} ≤ 1/4 with 4 | s → any locally invertible outer graph with ports F_2^m and expansion ≤ λ², any Cayley inner graph on (F_2^m)^s with q ≥ 1 generators and expansion ≤ λ, any 0 < λ ≤ 1/4, s ≥ 1; reason: the argument uses only these properties; the source's graphs satisfy them, so the statement specializes to the source's
--   - encoding: walk distributions WRW^k_s(a,b) and ←WRW^r_s(a,b) → averages over the latent generator indices; the reverse walk is the forward walk with r edges conditioned on (a_r, b_r) = (a, b); reason: the source defines ←WRW^r_s(a,b) as the walks with (a_r, b_r) = (a, b); same law
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 24 (PDF p. 27), Appendix B.6, Claim 16

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 16 (Appendix B.6, p. 24): `τ_{k+1}² ≤ μ_k² + λ² τ_k²` for `0 ≤ k ≤ t - 1`. -/
theorem claim16_forward_variance {A : Type} [Fintype A] [Nonempty A] {m s q D : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)
    (lam : ℝ) (t : ℕ) (hs : 0 < s) (hq : 0 < q) (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hinv : G.LocallyInvertible) (hA : G.IsExpander (lam ^ 2)) (hB : (cayley u).IsExpander lam)
    (hU : ∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1) :
    ∀ k : ℕ, k + 1 ≤ t → tauSq G u U (k + 1) ≤ muSq G u U k + lam ^ 2 * tauSq G u U k := by sorry

end ExpanderWalkDecode.Main
