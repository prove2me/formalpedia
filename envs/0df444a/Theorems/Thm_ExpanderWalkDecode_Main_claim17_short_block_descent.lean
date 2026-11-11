-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim17_short_block_descent
-- name    : ExpanderWalkDecode.Main.claim17_short_block_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:35.401189+00:00
-- url     : https://prove2.me/theorems/94d63cbc-4bf6-483a-a842-ade1904e9dca
-- title:
--   Claim 17 — short-block descent $\mu_{k+r}^2\le38(19\lambda^2)^{r-2}\Phi_k$ when $\|M_0\|_{\mathrm{op}}<4\lambda$
-- statement:
--   Let $A$ be a locally invertible outer graph with ports $\mathbb F_2^m$ and expansion at most $\lambda^2$, $B$ a Cayley graph on $(\mathbb F_2^m)^s$ ($s\ge1$) with $q\ge1$ generators and expansion at most $\lambda$, where $0<\lambda\le1/4$, and let $\{U_a\}_{a\in A}$ be real symmetric orthogonal $D\times D$ matrices. Let $f_k, M_k(a), M_k, \tau_k^2, \mu_k^2, \Phi_k, g_{r,k}, N_{r,k}(a), N_{r,k}, \sigma^2_{r,k}, \Psi_{r,k}$ be the quantities of Appendix B.6 built from the wide replacement walks of $A$ and $B$ and from $U$.
--   If $\|M_0\|_{\mathrm{op}}<4\lambda$, then for all $1\le r\le s$ and $0\le k\le t-r$,
--   $$\mu_{k+r}^2\le 38\,(19\lambda^2)^{r-2}\,\Phi_k .$$
--   For $r=1$ the power is $(19\lambda^2)^{-1}$.
--
--   Together with Claim 16 this gives the geometric decay of $\Phi$ along blocks of $s$ steps that proves Lemma 4.
--
--   Differences from the source:
--   - generalization: the construction's graphs: A from Proposition 4 (2^s-regular), B from Proposition 5 on F_2^{s^2} with 2^{s/2} generators, λ = (s²−1)2^{−s/4} ≤ 1/4 with 4 | s → any locally invertible outer graph with ports F_2^m and expansion ≤ λ², any Cayley inner graph on (F_2^m)^s with q ≥ 1 generators and expansion ≤ λ, any 0 < λ ≤ 1/4, s ≥ 1; reason: the argument uses only these properties; the source's graphs satisfy them, so the statement specializes to the source's
--   - encoding: walk distributions WRW^k_s(a,b) and ←WRW^r_s(a,b) → averages over the latent generator indices; the reverse walk is the forward walk with r edges conditioned on (a_r, b_r) = (a, b); reason: the source defines ←WRW^r_s(a,b) as the walks with (a_r, b_r) = (a, b); same law
--   - encoding: (19λ²)^{r−2} → integer power (19λ²)^((r:ℤ)−2); reason: the exponent is negative at r = 1; natural-number subtraction would truncate it
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 24 (PDF p. 27), Appendix B.6, Claim 17

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 17 (Appendix B.6, p. 24): if `‖M_0‖_op < 4λ`, then for `1 ≤ r ≤ s` and
`0 ≤ k ≤ t - r`, `μ_{k+r}² ≤ 38 (19λ²)^{r-2} Φ_k` (an integer power: `r = 1` gives `(19λ²)^{-1}`). -/
theorem claim17_short_block_descent {A : Type} [Fintype A] [Nonempty A] {m s q D : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)
    (lam : ℝ) (t : ℕ) (hs : 0 < s) (hq : 0 < q) (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hinv : G.LocallyInvertible) (hA : G.IsExpander (lam ^ 2)) (hB : (cayley u).IsExpander lam)
    (hU : ∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1) (hM0 : opNorm (Mk G u U 0) < 4 * lam) :
    ∀ r k : ℕ, 1 ≤ r → r ≤ s → k + r ≤ t →
      muSq G u U (k + r) ≤ 38 * (19 * lam ^ 2) ^ ((r : ℤ) - 2) * Phi G u U lam k := by sorry

end ExpanderWalkDecode.Main
