-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_lemma4_10_visitation_ratios
-- name    : CorruptRobustRL.Supervised.lemma4_10_visitation_ratios
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:12.341269+00:00
-- url     : https://prove2.me/theorems/f20ece49-f6d0-4ae2-bc96-4b25a2b3c824
-- title:
--   Lemma 4.10, p. 19 — UCB visitation ratios $\rho_\ell\le4eH\ell$, $\rho_{\le\ell}\le2\cdot2^\ell eH\ell$ and $\rho_{\le\ell_\star}\le4eCH\log_2(2C)$
-- statement:
--   Fix the nominal MDP, a horizon $H\ge1$, $\ell_{\max}$ layers and arbitrary deterministic base policies $\pi^{\mathrm{base}}_\ell$. Let $\pi^{\mathrm{master}}_\ell$ and $\pi^{\mathrm{master}}_{\le\ell}$ be the conditioned master policies of Definition 4.6. Then, for every layer $\ell\in[\ell_{\max}]$:
--
--   1. $\pi^{\mathrm{master}}_\ell$ has UCB visitation ratio at most $4eH\ell$ with respect to the UCB policy $\pi^{\mathrm{base}}_\ell$;
--   2. $\pi^{\mathrm{master}}_{\le\ell}$ has UCB visitation ratio at most $2\cdot2^\ell eH\ell$ with respect to $\pi^{\mathrm{base}}_\ell$;
--   3. for every integer $C$ with $1\le C\le2^{\ell_{\max}}$ and $\ell_\star=\min\{\ell\ge1:2^\ell\ge C\}$, $\pi^{\mathrm{master}}_{\le\ell_\star}$ has UCB visitation ratio at most
--   $$4eCH\log_2(2C)$$
--   with respect to $\pi^{\mathrm{base}}_{\ell_\star}$.
--
--   These are the constants that Theorem 4.1 multiplies into the bonus sums.
--
--   **Formalization Note** The visitation ratio involves only the policies and the MDP, so the Q-supervisor $\mathcal T_\ell$ enters only through its UCB policy $\pi^{\mathrm{base}}_\ell$, which is taken arbitrary. The ratio is required for every schedule prefix, as Definition 4.4 demands for a mixture of deterministic policies; the printed proof bounds the marginal probability $P[\ell_h=\dots=\ell_H=\ell\mid\ell_H=\ell]$. The logarithm is base 2: $\ell_\star\le\log_2(2C)$ follows from $2^{\ell_\star}\le2C$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 19, Lemma 4.10; proof pp. 19–20

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Lemma 4.10 (p. 19): for any base policies, the UCB visitation ratio of `π^master_ℓ` with respect
to the UCB policy `π^base_ℓ` is at most `4eHℓ`, that of `π^master_{≤ℓ}` is at most `2·2^ℓ eHℓ`, and
that of `π^master_{≤ℓ⋆}` is at most `4eCH log₂(2C)`. -/
theorem lemma4_10_visitation_ratios
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (base : ℕ → DetPolicy X A) :
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      HasVisitRatio M H (masterEq H ℓmax base ℓ) (base ℓ) (4 * Real.exp 1 * H * ℓ)) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      HasVisitRatio M H (masterLe H ℓmax base ℓ) (base ℓ) (2 * 2 ^ ℓ * Real.exp 1 * H * ℓ)) ∧
    (∀ C : ℕ, 1 ≤ C → C ≤ 2 ^ ℓmax →
      HasVisitRatio M H (masterLe H ℓmax base (lstar C)) (base (lstar C))
        (4 * Real.exp 1 * C * H * Real.logb 2 (2 * C))) := by sorry

end CorruptRobustRL.Supervised
