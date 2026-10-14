-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_lemma4_6_admissible_of_valid
-- name    : CorruptRobustRL.Supervised.lemma4_6_admissible_of_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:48.607375+00:00
-- url     : https://prove2.me/theorems/4e57c0ee-2dd8-4128-8505-210067de4c1f
-- title:
--   Lemma 4.6, p. 18 — valid global and subsampled model-estimates for every learner $\ell\ge\ell_\star$ make each $\mathcal T_\ell$, $\ell\ge\ell_\star$, confidence-admissible
-- statement:
--   Consider one episode of SuperVIsed.C on the nominal MDP with horizon $H\ge1$: the learners $\ell=\ell_{\max},\dots,1$ run UCBVI-BASE with nested active sets, each with its global model-estimate $\mathfrak m_{\mathrm{gl},\ell}$ and its subsampled model-estimate $\mathfrak m_{\mathrm{sb},\ell}$ (both with the tabular ranges), and with any argmax selector. Let $\mathcal T_\ell$ be the Q-supervisor of learner $\ell$.
--
--   Fix $\ell_\star\in\{1,\dots,\ell_{\max}\}$. If, for every $\ell$ with $\ell_\star\le\ell\le\ell_{\max}$, both $\mathfrak m_{\mathrm{gl},\ell}$ and $\mathfrak m_{\mathrm{sb},\ell}$ are valid with respect to $\mathcal T_\ell$, then
--   $$\mathcal T_\ell\ \text{is confidence-admissible for every }\ell_\star\le\ell\le\ell_{\max}.$$
--
--   Validity is a statement about bonuses; this lemma turns it into the optimism and the correct elimination that the regret decomposition needs.
--
--   **Formalization Note** The page writes "Fix $\ell_\star\in[\log K]$"; the layers are $[\ell_{\max}]$, and the Lean statement takes $1\le\ell_\star\le\ell_{\max}$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 18, Lemma 4.6; proof App. D.2, pp. 55–56

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Lemma 4.6 (p. 18): if the global and subsampled model-estimates of every learner
`ℓ ∈ [ℓ⋆, ℓmax]` are valid with respect to that learner's Q-supervisor `𝒯_ℓ`, then every such
`𝒯_ℓ` is confidence-admissible. -/
theorem lemma4_6_admissible_of_valid
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (E : EpisodeEst X A)
    (hrange : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax → (E.gl ℓ).IsModelEst H ∧ (E.sb ℓ).IsModelEst H)
    (sel : Selector A) (hsel : IsArgmaxSelector sel)
    (lst : ℕ) (hlst : 1 ≤ lst) (hlstmax : lst ≤ ℓmax)
    (hvalid : ∀ ℓ, lst ≤ ℓ → ℓ ≤ ℓmax →
      (E.gl ℓ).IsValid M H (layerSup H ℓmax E sel ℓ) ∧
        (E.sb ℓ).IsValid M H (layerSup H ℓmax E sel ℓ)) :
    ∀ ℓ, lst ≤ ℓ → ℓ ≤ ℓmax → IsAdmissible M H (layerSup H ℓmax E sel ℓ) := by sorry

end CorruptRobustRL.Supervised
