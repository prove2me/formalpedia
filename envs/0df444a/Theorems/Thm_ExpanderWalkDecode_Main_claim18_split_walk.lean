-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim18_split_walk
-- name    : ExpanderWalkDecode.Main.claim18_split_walk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:53.785198+00:00
-- url     : https://prove2.me/theorems/19a7282b-acfb-4404-b6ed-8258902a1653
-- title:
--   Claim 18 — split-walk bound $\mu_{k+r}^2\le\|\mathbb E_a M_k(a)^{\mathsf T}N_{r,k+r}(a)\|_{\mathrm{op}}+\lambda\tau_k\sigma_{r,k+r}$
-- statement:
--   Let $A$ be a locally invertible outer graph with ports $\mathbb F_2^m$ and expansion at most $\lambda^2$, $B$ a Cayley graph on $(\mathbb F_2^m)^s$ ($s\ge1$) with $q\ge1$ generators and expansion at most $\lambda$, where $0<\lambda\le1/4$, and let $\{U_a\}_{a\in A}$ be real symmetric orthogonal $D\times D$ matrices. Let $f_k, M_k(a), M_k, \tau_k^2, \mu_k^2, \Phi_k, g_{r,k}, N_{r,k}(a), N_{r,k}, \sigma^2_{r,k}, \Psi_{r,k}$ be the quantities of Appendix B.6 built from the wide replacement walks of $A$ and $B$ and from $U$.
--   Then for all $1\le r\le s$ and $0\le k\le t-r$,
--   $$\mu_{k+r}^2\le\big\|\mathbb E_a[M_k(a)^{\mathsf T}N_{r,k+r}(a)]\big\|_{\mathrm{op}}+\lambda\,\tau_k\,\sigma_{r,k+r}.$$
--
--   The bound splits a walk of length $k+r$ into a reverse part of length $r$ and a forward part of length $k$, and is the first step in bounding $\mu_{k+r}$ (Claim 20).
--
--   Differences from the source:
--   - generalization: the construction's graphs: A from Proposition 4 (2^s-regular), B from Proposition 5 on F_2^{s^2} with 2^{s/2} generators, λ = (s²−1)2^{−s/4} ≤ 1/4 with 4 | s → any locally invertible outer graph with ports F_2^m and expansion ≤ λ², any Cayley inner graph on (F_2^m)^s with q ≥ 1 generators and expansion ≤ λ, any 0 < λ ≤ 1/4, s ≥ 1; reason: the argument uses only these properties; the source's graphs satisfy them, so the statement specializes to the source's
--   - encoding: walk distributions WRW^k_s(a,b) and ←WRW^r_s(a,b) → averages over the latent generator indices; the reverse walk is the forward walk with r edges conditioned on (a_r, b_r) = (a, b); reason: the source defines ←WRW^r_s(a,b) as the walks with (a_r, b_r) = (a, b); same law
--   - encoding: τ_k and σ_{r,k} → square roots of τ_k² and σ_{r,k}²; reason: τ_k², σ_{r,k}² are defined first; same quantities
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 25 (PDF p. 28), Appendix B.6, Claim 18

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 18 (Appendix B.6, p. 25): for `1 ≤ r ≤ s` and `0 ≤ k ≤ t - r`,
`μ_{k+r}² ≤ ‖E_a[M_k(a)ᵀ N_{r,k+r}(a)]‖_op + λ τ_k σ_{r,k+r}`. -/
theorem claim18_split_walk {A : Type} [Fintype A] [Nonempty A] {m s q D : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)
    (lam : ℝ) (t : ℕ) (hs : 0 < s) (hq : 0 < q) (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hinv : G.LocallyInvertible) (hA : G.IsExpander (lam ^ 2)) (hB : (cayley u).IsExpander lam)
    (hU : ∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1) :
    ∀ r k : ℕ, 1 ≤ r → r ≤ s → k + r ≤ t →
      muSq G u U (k + r) ≤
        opNorm (avg fun a : A => (Mka G u U k a)ᵀ * Nrka G u U r (k + r) a)
          + lam * Real.sqrt (tauSq G u U k) * Real.sqrt (sigmaSq G u U r (k + r)) := by sorry

end ExpanderWalkDecode.Main
