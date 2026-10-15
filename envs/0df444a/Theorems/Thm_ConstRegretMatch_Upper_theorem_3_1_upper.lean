-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_theorem_3_1_upper
-- name    : ConstRegretMatch.Upper.theorem_3_1_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:49.972342+00:00
-- url     : https://prove2.me/theorems/192e5b8c-c48b-4004-a321-3ccdfedfde21
-- title:
--   Theorem 3.1 (Upper bound), p. 14 — the exhaustive resolving policy with τ = ⌈κϵ⁻¹⌉ has 𝓡^{*,t} − 𝓡^{D,t} ≤ Γϵ⁻¹ for all t
-- statement:
--   Fix the topology of a matching network ($n$ agent types, $d$ matches, matching matrix $M$) and match values $r_m>0$. There are constants $\kappa>0$ and $\Gamma>0$, depending only on $n$, $d$, $M$ and $r$ (not on $\lambda$ or $\epsilon$), with the following property.
--
--   Let $\lambda$ be an arrival law under which the network satisfies the general position condition, with optimal solution $(z^*,s^*)$ of (SPP) and general position gap $\epsilon$. Let $D$ be the exhaustive resolving policy with inter-action delay
--   $$\tau=\lceil\kappa\epsilon^{-1}\rceil,$$
--   redundant matches removed, leftovers of the under-demanded queues removed after each epoch, and any tie-breaking rule in (3). Then $D$ is an admissible matching policy and
--   $$\mathcal R^{*,t}-\mathcal R^{D,t}\le\Gamma\epsilon^{-1}\qquad\text{for all } t\ge1. \tag{Upper bound}$$
--
--   The regret against the hindsight benchmark is thus bounded uniformly in time, and the bound scales with the inverse of the general position gap; the companion lower bound of the paper shows this order cannot be improved for non-trivial networks.
--
--   **Formalization Note** Time is discrete and "for all $t>0$" is $t\ge1$ (at $t=0$ both values are $0$). The quantifier order is the paper's: $\kappa$ and $\Gamma$ are chosen after the topology and $r$ and before $\lambda$, the GP solution, the tie-breaking rule and $t$. The existential "there exists a matching policy $D$" is witnessed by the exhaustive resolving policy itself, for every tie-breaking rule. Admissible policies never reject agents; the resolving policy's removals act on its virtual queue, and its matches are feasible in the market without removals, hence admissible. (3) is solved with the redundant matches set to zero.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 14, Theorem 3.1 (Upper bound); proof App. D, pp. 48–49

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy
import Definitions.Def_ConstRegretMatch_Upper_Resolving

namespace ConstRegretMatch.Upper

/-- Theorem 3.1 (Upper bound), p. 14. Fix the network and the match values. There are constants
`κ > 0` and `Γ > 0`, depending only on the network and `r` (not on `λ` or `ϵ`), such that for every
arrival law `λ` satisfying GP with solution `(z*, s*)` and gap `ϵ`, and every tie-breaking selection
for (3), the exhaustive resolving policy with inter-action delay `τ = ⌈κϵ⁻¹⌉` is an admissible
matching policy and `𝓡^{*,t} - 𝓡^{D,t} ≤ Γϵ⁻¹` for all `t ≥ 1`. -/
theorem theorem_3_1_upper {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : IsMatchValues r) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ Γ : ℝ, 0 < Γ ∧
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
      ∀ sel : (Fin n → ℕ) → Fin d → ℕ, IsResolvingSelection N r (Mzero z) sel →
        IsAdmissible N (resolvingPolicy N sel (Qplus s) ⌈κ / gpGap z s⌉₊) ∧
        ∀ t : ℕ, 1 ≤ t →
          Rstar N lam r t - valueOf lam r (resolvingPolicy N sel (Qplus s) ⌈κ / gpGap z s⌉₊) t
            ≤ Γ / gpGap z s := by sorry

end ConstRegretMatch.Upper
