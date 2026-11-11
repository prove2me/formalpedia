-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_lemma4_level_t_implies_level_0
-- name    : ExpanderWalkDecode.Main.lemma4_level_t_implies_level_0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:34.620849+00:00
-- url     : https://prove2.me/theorems/bc8a9d94-7340-4eca-b5bb-e59984c874e5
-- title:
--   Lemma 4 — level-$t$ agreement implies level-$0$ agreement $\|\mathbb E_aU_a\|_{\mathrm{op}}\ge4\lambda$
-- statement:
--   Let $A$ be a locally invertible outer graph with ports $\mathbb F_2^m$ and expansion at most $\lambda^2$, $B$ a Cayley graph on $(\mathbb F_2^m)^s$ ($s\ge1$) with $q\ge1$ generators and expansion at most $\lambda$, where $0<\lambda\le1/4$, and let $\{U_a\}_{a\in A}$ be real symmetric orthogonal $D\times D$ matrices. Let $f_k, M_k(a), M_k, \tau_k^2, \mu_k^2, \Phi_k, g_{r,k}, N_{r,k}(a), N_{r,k}, \sigma^2_{r,k}, \Psi_{r,k}$ be the quantities of Appendix B.6 built from the wide replacement walks of $A$ and $B$ and from $U$. Write $H(s,t)=2\,(1/(9\lambda^4))^{1+t/s}(19\lambda^2)^t$. If
--   $$\big\|\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}[U_{a_0}\cdots U_{a_t}]\big\|_{\mathrm{op}}^2\ge H(s,t),$$
--   then
--   $$\big\|\mathbb E_{a\sim A}[U_a]\big\|_{\mathrm{op}}\ge4\lambda .$$
--
--   This is the operator-amplification property of the wide replacement product: a large correlation along wide replacement walks forces a large correlation at a single vertex. It turns the level-$t$ agreement of the recovered parity operators into the level-$0$ agreement used by the rounding step.
--
--   Differences from the source:
--   - generalization: the construction's graphs: A from Proposition 4 (2^s-regular), B from Proposition 5 on F_2^{s^2} with 2^{s/2} generators, λ = (s²−1)2^{−s/4} ≤ 1/4 with 4 | s → any locally invertible outer graph with ports F_2^m and expansion ≤ λ², any Cayley inner graph on (F_2^m)^s with q ≥ 1 generators and expansion ≤ λ, any 0 < λ ≤ 1/4, s ≥ 1; reason: the argument uses only these properties; the source's graphs satisfy them, so the statement specializes to the source's
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 24 (PDF p. 27), Appendix B.6, Lemma 4

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Lemma 4 (Appendix B.6, p. 24): for real symmetric orthogonal `U_a`, if
`‖E_{⃗a ∼ WRW^t_s} [U_{a₀} ⋯ U_{a_t}]‖_op² ≥ 2 (1/(9λ⁴))^{1+t/s} (19λ²)^t`, then
`‖E_{a ∼ A} [U_a]‖_op ≥ 4λ`. -/
theorem lemma4_level_t_implies_level_0 {A : Type} [Fintype A] [Nonempty A] {m s q D : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)
    (lam : ℝ) (t : ℕ) (hs : 0 < s) (hq : 0 < q) (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hinv : G.LocallyInvertible) (hA : G.IsExpander (lam ^ 2)) (hB : (cayley u).IsExpander lam)
    (hU : ∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1)
    (hamp : ampThreshold lam s t ≤ opNorm (wrwAvg G u t (prodU U)) ^ 2) :
    4 * lam ≤ opNorm (avg U) := by sorry

end ExpanderWalkDecode.Main
