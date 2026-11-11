-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim21_reverse_descent
-- name    : ExpanderWalkDecode.Main.claim21_reverse_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:23.534159+00:00
-- url     : https://prove2.me/theorems/ba7e9965-2506-40f0-a61f-c634b9d46f6e
-- title:
--   Claim 21 — reverse-potential descent $\Psi_{r,\ell}\le(\|M_0\|_{\mathrm{op}}^2+3\lambda^2)^{r-1}\Psi_{1,\ell}$
-- statement:
--   Let $A$ be a locally invertible outer graph with ports $\mathbb F_2^m$ and expansion at most $\lambda^2$, $B$ a Cayley graph on $(\mathbb F_2^m)^s$ ($s\ge1$) with $q\ge1$ generators and expansion at most $\lambda$, where $0<\lambda\le1/4$, and let $\{U_a\}_{a\in A}$ be real symmetric orthogonal $D\times D$ matrices. Let $f_k, M_k(a), M_k, \tau_k^2, \mu_k^2, \Phi_k, g_{r,k}, N_{r,k}(a), N_{r,k}, \sigma^2_{r,k}, \Psi_{r,k}$ be the quantities of Appendix B.6 built from the wide replacement walks of $A$ and $B$ and from $U$.
--   Then for all $1\le r\le s$ and $r\le\ell\le t$,
--   $$\Psi_{r,\ell}\le\big(\|M_0\|_{\mathrm{op}}^2+3\lambda^2\big)^{r-1}\,\Psi_{1,\ell}.$$
--
--   Differences from the source:
--   - generalization: the construction's graphs: A from Proposition 4 (2^s-regular), B from Proposition 5 on F_2^{s^2} with 2^{s/2} generators, λ = (s²−1)2^{−s/4} ≤ 1/4 with 4 | s → any locally invertible outer graph with ports F_2^m and expansion ≤ λ², any Cayley inner graph on (F_2^m)^s with q ≥ 1 generators and expansion ≤ λ, any 0 < λ ≤ 1/4, s ≥ 1; reason: the argument uses only these properties; the source's graphs satisfy them, so the statement specializes to the source's
--   - encoding: walk distributions WRW^k_s(a,b) and ←WRW^r_s(a,b) → averages over the latent generator indices; the reverse walk is the forward walk with r edges conditioned on (a_r, b_r) = (a, b); reason: the source defines ←WRW^r_s(a,b) as the walks with (a_r, b_r) = (a, b); same law
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 27 (PDF p. 30), Appendix B.6, Claim 21

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 21 (Appendix B.6, p. 27): for `1 ≤ r ≤ s` and `r ≤ ℓ ≤ t`,
`Ψ_{r,ℓ} ≤ (‖M_0‖_op² + 3λ²)^{r-1} Ψ_{1,ℓ}`. -/
theorem claim21_reverse_descent {A : Type} [Fintype A] [Nonempty A] {m s q D : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)
    (lam : ℝ) (t : ℕ) (hs : 0 < s) (hq : 0 < q) (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hinv : G.LocallyInvertible) (hA : G.IsExpander (lam ^ 2)) (hB : (cayley u).IsExpander lam)
    (hU : ∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1) :
    ∀ r ℓ : ℕ, 1 ≤ r → r ≤ s → r ≤ ℓ → ℓ ≤ t →
      Psi G u U lam r ℓ ≤
        (opNorm (Mk G u U 0) ^ 2 + 3 * lam ^ 2) ^ (r - 1) * Psi G u U lam 1 ℓ := by sorry

end ExpanderWalkDecode.Main
