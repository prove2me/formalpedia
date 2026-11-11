-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim19_reverse_outer_mixing
-- name    : ExpanderWalkDecode.Main.claim19_reverse_outer_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:19.835835+00:00
-- url     : https://prove2.me/theorems/6f8c928c-efb7-4d67-8f39-0bdb52e9131f
-- title:
--   Claim 19 — outer mixing for reverse moments, with the factor $\lambda^2$
-- statement:
--   Let $A$ be a locally invertible outer graph with ports $\mathbb F_2^m$ and expansion at most $\lambda^2$, $B$ a Cayley graph on $(\mathbb F_2^m)^s$ ($s\ge1$) with $q\ge1$ generators and expansion at most $\lambda$, where $0<\lambda\le1/4$, and let $\{U_a\}_{a\in A}$ be real symmetric orthogonal $D\times D$ matrices. Let $f_k, M_k(a), M_k, \tau_k^2, \mu_k^2, \Phi_k, g_{r,k}, N_{r,k}(a), N_{r,k}, \sigma^2_{r,k}, \Psi_{r,k}$ be the quantities of Appendix B.6 built from the wide replacement walks of $A$ and $B$ and from $U$.
--   Then for all $1\le r\le s$ and $0\le k,\ell\le t$,
--   $$\big\|\mathbb E_a[M_k(a)^{\mathsf T}N_{r,\ell}(a)]\big\|_{\mathrm{op}}\le\big\|M_k^{\mathsf T}N_{r,\ell}\big\|_{\mathrm{op}}+\lambda^2\,\tau_k\,\sigma_{r,\ell}.$$
--
--   Combined with Claim 18 it yields Claim 20.
--
--   Differences from the source:
--   - generalization: the construction's graphs: A from Proposition 4 (2^s-regular), B from Proposition 5 on F_2^{s^2} with 2^{s/2} generators, λ = (s²−1)2^{−s/4} ≤ 1/4 with 4 | s → any locally invertible outer graph with ports F_2^m and expansion ≤ λ², any Cayley inner graph on (F_2^m)^s with q ≥ 1 generators and expansion ≤ λ, any 0 < λ ≤ 1/4, s ≥ 1; reason: the argument uses only these properties; the source's graphs satisfy them, so the statement specializes to the source's
--   - encoding: walk distributions WRW^k_s(a,b) and ←WRW^r_s(a,b) → averages over the latent generator indices; the reverse walk is the forward walk with r edges conditioned on (a_r, b_r) = (a, b); reason: the source defines ←WRW^r_s(a,b) as the walks with (a_r, b_r) = (a, b); same law
--   - encoding: τ_k and σ_{r,k} → square roots of τ_k² and σ_{r,k}²; reason: τ_k², σ_{r,k}² are defined first; same quantities
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 26 (PDF p. 29), Appendix B.6, Claim 19

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 19 (Appendix B.6, p. 26): for `1 ≤ r ≤ s` and `0 ≤ k, ℓ ≤ t`,
`‖E_a[M_k(a)ᵀ N_{r,ℓ}(a)]‖_op ≤ ‖M_kᵀ N_{r,ℓ}‖_op + λ² τ_k σ_{r,ℓ}`. -/
theorem claim19_reverse_outer_mixing {A : Type} [Fintype A] [Nonempty A] {m s q D : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)
    (lam : ℝ) (t : ℕ) (hs : 0 < s) (hq : 0 < q) (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hinv : G.LocallyInvertible) (hA : G.IsExpander (lam ^ 2)) (hB : (cayley u).IsExpander lam)
    (hU : ∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1) :
    ∀ r k ℓ : ℕ, 1 ≤ r → r ≤ s → k ≤ t → ℓ ≤ t →
      opNorm (avg fun a : A => (Mka G u U k a)ᵀ * Nrka G u U r ℓ a) ≤
        opNorm ((Mk G u U k)ᵀ * Nrk G u U r ℓ)
          + lam ^ 2 * Real.sqrt (tauSq G u U k) * Real.sqrt (sigmaSq G u U r ℓ) := by sorry

end ExpanderWalkDecode.Main
