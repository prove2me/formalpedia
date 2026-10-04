-- Prove2me | Theorems.Thm_DemandResponse_SecondBest_lemmaA1_F0
-- name    : DemandResponse.SecondBest.lemmaA1_F0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:42:08.965893+00:00
-- url     : https://prove2.me/theorems/0e955e56-0ce7-4d43-89c2-8247aca72a65
-- title:
--   Lemma A.1 — $F_0(q)=f_0(q,-q)=-2H_v(-q)$ is non-decreasing
-- statement:
--   Let $f_0(q,\gamma):=q|\hat\sigma(\gamma)|^2+\hat c_2(\gamma)$ be the total cost of volatility borne by the producer when the unit cost of volatility is $q$ and the payment rate for volatility reduction is $\gamma$ ((A.10)), and let
--   $$F_0(q):=\inf_{\gamma\le0}f_0(q,\gamma).$$
--   Then for every real $q$,
--   $$F_0(q)=f_0(q,-q)=-2H_v(-q),$$
--   and $F_0$ is non-decreasing on $\mathbb R$.
--
--   The lemma eliminates the volatility payment $\gamma$ from the producer's problem: the optimal $\gamma$ equals minus the producer's unit cost of volatility, and what remains is a monotone function of that cost. This is what turns the producer's HJB equation (A.11) into a scalar minimisation over $z$.
--
--   **Formalization Note.** The statement is for every real $q$, without a sign hypothesis; for $q<0$ the point $-q$ lies outside $\{\gamma\le0\}$, but $\hat b(-q)=\hat b(0)$ so the identity still holds.
-- source:
--   arXiv:1810.09063v3, Appendix A.3, (A.10) and Lemma A.1 (p. 29)

import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

/-- Lemma A.1 (arXiv:1810.09063v3, p. 29): `F₀(q) = f₀(q, -q) = -2 H_v(-q)`, and `F₀` is
non-decreasing. Stated for every real `q`. -/
theorem lemmaA1_F0 {N d : ℕ} (P : Params N d) :
    (∀ q : ℝ, F0 P q = f0 P q (-q) ∧ f0 P q (-q) = -2 * Hv P (-q)) ∧ Monotone (F0 P) := by sorry

end DemandResponse.SecondBest
