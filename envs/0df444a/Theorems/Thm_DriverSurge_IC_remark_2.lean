-- Prove2me | Theorems.Thm_DriverSurge_IC_remark_2
-- name    : DriverSurge.IC.remark_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:12.198819+00:00
-- url     : https://prove2.me/theorems/4bdd1c41-36ea-4cd8-95eb-a2439cd3305f
-- title:
--   Remark 2, p. 57 — for w_i(u) = mu + zq_{i→j}(u), W_i = m(T_i − 1) + z(Q_i − λ_{i→j}) and uT_iT_j·r equals q_{i→j}(u)[…] + u[…]
-- statement:
--   Let $\sigma$ be a policy with $\tau$ $F_k$-integrable on $\sigma_k$ and $w_j$ $F_j$-integrable on $\sigma_j$, and let the payment in state $i$ be
--   $$w_i(u)=mu+z\,q_{i\to j}(u).$$
--   Then
--   $$W_i=m(T_i-1)+z(Q_i-\lambda_{i\to j}),$$
--   and for every $u>0$
--   $$u\,T_iT_j\,r(u,i,w,\sigma)=q_{i\to j}(u)\big[(R_j-m)T_jT_i+mT_j+zQ_jT_i+zT_j\lambda_{i\to j}\big]+u\big[Q_iT_j(m-R_j)+Q_j(m-zQ_i+z\lambda_{i\to j})\big],$$
--   so $\partial R(w,\sigma)/\partial u$, which has the sign of $r$, has the sign of the right-hand side.
--
--   These two identities are the algebra behind the windows of Lemmas 9 and 10 and the targets of Theorem 3.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$.
--
--   Differences from the source:
--   - generalization: $\partial R/\partial u\propto q_{i\to j}(u)[\dots]+u[\dots]$ → the exact identity $uT_iT_j\,r=q_{i\to j}(u)[\dots]+u[\dots]$, together with the sign statement; reason: $uT_iT_j>0$, so the identity implies the printed sign claim
--   - encoding: $T_i$, $R_j$ with integrals implicitly finite → $\tau$ $F_k$-integrable on $\sigma_k$ and $w_j$ $F_j$-integrable on $\sigma_j$; reason: the quantities are undefined otherwise; only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the identities hold for all trip-length laws and payments, so they specialize to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Remark 2

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 2 (p. 57). Let `σ` be a policy with `τ` integrable on `σ_1`, `σ_2` and `w_j` integrable on
`σ_j`, and let `w_i(u) = mu + zq_{i→j}(u)`. Then `W_i = m(T_i − 1) + z(Q_i − λ_{i→j})`, and for `u > 0`
`u T_iT_j · r(u, i, w, σ) = q_{i→j}(u)[(R_j − m)T_jT_i + mT_j + zQ_jT_i + zT_jλ_{i→j}] + u[Q_iT_j(m − R_j) + Q_j(m − zQ_i + zλ_{i→j})]`,
so `∂/∂u R(w, σ)` (which has the sign of `r`) has the sign of the right-hand side. -/
theorem remark_2 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k)) (i : Fin 2)
    (hwj : IntegrableOn (w (other i)) (σ (other i)) (P.F (other i))) (m z : ℝ)
    (hwi : w i = fun u => m * u + z * q P i u) :
    Wn P i (w i) (σ i) = m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i) ∧
    ∀ u : ℝ, 0 < u →
      u * Tn P i (σ i) * Tn P (other i) (σ (other i)) * rFun P w σ i u =
          q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i)) ∧
      SignType.sign (rFun P w σ i u) =
        SignType.sign (q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i))) := by sorry

end DriverSurge.IC
