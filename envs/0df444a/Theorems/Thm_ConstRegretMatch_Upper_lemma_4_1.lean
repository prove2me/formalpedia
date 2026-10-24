-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_lemma_4_1
-- name    : ConstRegretMatch.Upper.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:59.830979+00:00
-- url     : https://prove2.me/theorems/0505cc4a-37a8-41a7-b68e-9fc1f41f4574
-- title:
--   Lemma 4.1, p. 19 — optimality test: no ℳ₀ matches and 𝔼[Qᵢᵗ] = O(ϵ⁻¹) on 𝒬₀ give 𝓡^{*,t} − 𝓡^{D,t} = O(ϵ⁻¹)
-- statement:
--   Fix the topology of a matching network and match values $r>0$, and let $C\ge0$. There is a constant $C'\ge0$, depending only on $C$, the topology and $r$, with the following property.
--
--   Let $\lambda$ be an arrival law under which the network satisfies GP, with optimal solution $(z^*,s^*)$ and gap $\epsilon$. Let $D$ be an admissible matching policy that
--
--   1. never performs a redundant match: $D^t_m=0$ for all $m\in\mathcal M_0$ and all $t$;
--   2. keeps the over-demanded queues short on average: $\mathbb E^D[Q^t_i]\le C\epsilon^{-1}$ for all $i\in\mathcal Q_0$ and all $t\ge1$.
--
--   Then
--   $$\mathcal R^{*,t}-\mathcal R^{D,t}\le C'\epsilon^{-1}\qquad\text{for all } t\ge1.$$
--
--   In words: under GP, a policy that avoids redundant matches and keeps the over-demanded queues of order $\epsilon^{-1}$ is hindsight optimal with regret of order $\epsilon^{-1}$. This reduces the upper bound of Theorem 3.1 to a bound on the queues in $\mathcal Q_0$.
--
--   **Formalization Note** The paper's $\mathcal O(\epsilon^{-1})$ in the hypothesis and in the conclusion are made explicit with the constants $C$ and $C'$; $C'$ is chosen before $\lambda$, $(z^*,s^*)$, $D$ and $t$, so it is uniform in all of them. Condition (i) of the paper, "does not reject any agents of type $i\in\mathcal Q_0$", holds for every admissible policy in this formalization, since admissible policies never reject agents. "For all $t>0$" is read in discrete time as $t\ge1$.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 19, Lemma 4.1 (optimality test); proof pp. 36–37

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy

namespace ConstRegretMatch.Upper

/-- Lemma 4.1 (optimality test), p. 19. Fix the network and the match values. For every constant
`C ≥ 0` there is a constant `C' ≥ 0` (depending only on `C`, the network and `r`) such that for every
arrival law `λ` satisfying GP with solution `(z*, s*)` and gap `ϵ`, every admissible policy `D` that
(ii) never performs a redundant match `m ∈ ℳ₀` and
(iii) has `𝔼[Q^t_i] ≤ C/ϵ` for every over-demanded type `i ∈ 𝒬₀` and every `t ≥ 1`
satisfies `𝓡^{*,t} - 𝓡^{D,t} ≤ C'/ϵ` for every `t ≥ 1`. Condition (i) (no rejection of `𝒬₀` agents)
holds for every admissible policy, which never rejects. -/
theorem lemma_4_1 {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ) (hr : IsMatchValues r) :
    ∀ C : ℝ, 0 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
      ∀ D : Policy n d, IsAdmissible N D →
        (∀ t ω, ∀ m ∈ Mzero z, D t ω m = 0) →
        (∀ t : ℕ, 1 ≤ t → ∀ i ∈ Qzero s,
          expect lam t (fun ω => (queue N D ω t i : ℝ)) ≤ C / gpGap z s) →
        ∀ t : ℕ, 1 ≤ t → Rstar N lam r t - valueOf lam r D t ≤ C' / gpGap z s := by sorry

end ConstRegretMatch.Upper
