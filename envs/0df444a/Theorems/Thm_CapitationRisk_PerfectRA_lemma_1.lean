-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_lemma_1
-- name    : CapitationRisk.PerfectRA.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:39.843838+00:00
-- url     : https://prove2.me/theorems/3975619c-ac09-49f7-b885-a378db2cf183
-- title:
--   Lemma 1, pp. 12–13 — the TM price P_s(w_s) of (3) induces quality w_s; boundary case (4) at w̲_s
-- statement:
--   Consider the Perfect Information Traditional Medicare provider of a service $s$ who is paid $P$ per unit of service and chooses quality $x \in [\underline w_s, 1]$ to maximize the payoff (2)
--   $$\pi_s(x) = D_s(x)\,P - C^f_s(x) - c_s\,D_s(x), \qquad D_s(x) = \sum_{i\in I}\lambda^s_i(x),$$
--   under the standing assumptions of the model. Let $P_s(x)$ be the TM price (3).
--
--   1. For every interior quality $\underline w_s < x < 1$ with $D_s'(x) > 0$ and every price $P$: $x$ is the unique maximizer of $\pi_s$ on $[\underline w_s,1]$ if and only if
--   $$P = P_s(x) = \big(D_s'(x)\big)^{-1}\Big(D_s'(x)\,c_s + \frac{dC^f_s(x)}{dx}\Big).$$
--   2. If $D_s'(1) > 0$, then under the price $P = P_s(1)$ the top quality $x = 1$ is the unique maximizer of $\pi_s$ on $[\underline w_s, 1]$.
--   3. At the minimum quality $x = \underline w_s$, for every price $P$: if
--   $$D_s'(\underline w_s)\,P = D_s'(\underline w_s)\,c_s + \frac{dC^f_s(\underline w_s)}{dx} - L_s \qquad (4)$$
--   for some Lagrange multiplier $L_s > 0$, then $\underline w_s$ is the unique maximizer of $\pi_s$ on $[\underline w_s,1]$; conversely, if $\underline w_s$ is the unique maximizer, then (4) holds for some $L_s \ge 0$.
--
--   This is the one-to-one correspondence between TM equilibrium quality and service reimbursement on which the whole paper rests: it justifies calling $P^*_s = P_s(w^*_s)$ the price that achieves the targeted quality $w^*_s$ in TM.
--
--   **Formalization Note.** In the converse of the lower-boundary case (4) the multiplier is $L_s \ge 0$, not $L_s > 0$: at $P = P_s(\underline w_s)$ the minimum quality is still the unique maximizer, with $L_s = 0$, so the page's strict sign holds only in the "if" direction. At $x = 1$ only the "if" direction is stated: every price above $P_s(1)$ also makes $1$ the maximizer, so the correspondence is one-to-one only in the interior. The hypothesis $D_s'(x) > 0$ is added so that the inverse in (3) is a genuine inverse.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 12–13, Lemma 1, eq. (3); proof p. 35

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA

open Model

/-- Lemma 1 (pp. 12–13): interior case (3), the upper end of the box, and the lower-boundary
case (4) with its Lagrange multiplier `L_s`. -/
theorem lemma_1 {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (M : Model S I) (hM : M.Standing) (s : S) :
    (∀ x ∈ Set.Ioo (M.wl s) 1, 0 < M.dDemand s x → ∀ P : ℝ,
      ((IsMaxOn (M.providerPayoff s P) (Set.Icc (M.wl s) 1) x ∧
        ∀ y ∈ Set.Icc (M.wl s) 1, IsMaxOn (M.providerPayoff s P) (Set.Icc (M.wl s) 1) y → y = x) ↔
        P = M.TMPrice s x)) ∧
    (0 < M.dDemand s 1 →
      IsMaxOn (M.providerPayoff s (M.TMPrice s 1)) (Set.Icc (M.wl s) 1) 1 ∧
        ∀ y ∈ Set.Icc (M.wl s) 1,
          IsMaxOn (M.providerPayoff s (M.TMPrice s 1)) (Set.Icc (M.wl s) 1) y → y = 1) ∧
    (∀ P : ℝ,
      ((∃ L : ℝ, 0 < L ∧ M.dDemand s (M.wl s) * P =
          M.dDemand s (M.wl s) * M.c s + deriv (M.Cf s) (M.wl s) - L) →
        IsMaxOn (M.providerPayoff s P) (Set.Icc (M.wl s) 1) (M.wl s) ∧
          ∀ y ∈ Set.Icc (M.wl s) 1,
            IsMaxOn (M.providerPayoff s P) (Set.Icc (M.wl s) 1) y → y = M.wl s) ∧
      ((IsMaxOn (M.providerPayoff s P) (Set.Icc (M.wl s) 1) (M.wl s) ∧
          ∀ y ∈ Set.Icc (M.wl s) 1,
            IsMaxOn (M.providerPayoff s P) (Set.Icc (M.wl s) 1) y → y = M.wl s) →
        ∃ L : ℝ, 0 ≤ L ∧ M.dDemand s (M.wl s) * P =
          M.dDemand s (M.wl s) * M.c s + deriv (M.Cf s) (M.wl s) - L)) := by sorry

end CapitationRisk.PerfectRA
