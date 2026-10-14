-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_lemma4_5_q_supervision
-- name    : CorruptRobustRL.Supervised.lemma4_5_q_supervision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:55.762681+00:00
-- url     : https://prove2.me/theorems/69f1a19d-ea1a-459d-85d1-a6d5c1a627ff
-- title:
--   Lemma 4.5, p. 17 — if admissible, $\mathcal T_{\ell_\star}$ supervises $\pi^{\mathrm{master}}_{\le\ell_\star}$ and $\mathcal T_\ell$ supervises $\pi^{\mathrm{master}}_{\ell}$
-- statement:
--   Consider one episode of SuperVIsed.C as in Lemma 4.6, with any argmax selector, and let $\mathcal T_\ell$ be the Q-supervisor of learner $\ell$ and $\pi^{\mathrm{master}}_\ell$, $\pi^{\mathrm{master}}_{\le\ell}$ the conditioned master policies built from the learners' base policies. Then:
--
--   1. for every $\ell_\star\in[\ell_{\max}]$, if $\mathcal T_{\ell_\star}$ is confidence-admissible, then $\pi^{\mathrm{master}}_{\le\ell_\star}$ is Q-supervised by $\mathcal T_{\ell_\star}$;
--   2. for every $\ell\in[\ell_{\max}]$, if $\mathcal T_\ell$ is confidence-admissible, then $\pi^{\mathrm{master}}_\ell$ is Q-supervised by $\mathcal T_\ell$.
--
--   Because the schedule is nondecreasing and the active sets are nested, the less robust learners only play actions that the supervising learner considers plausible.
--
--   **Formalization Note** The printed lemma has no hypothesis. Admissibility of the supervising learner is added: without it the learner's own action need not be plausible (its maximal upper estimate can fall below its maximal lower estimate when the two model-estimates disagree), and the statement is false. In Theorem 4.1 admissibility is supplied by Lemma 4.6.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 17, Lemma 4.5

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Lemma 4.5 (p. 17), under admissibility of the supervising learner: `π^master_{≤ℓ⋆}` is
supervised by `𝒯_{ℓ⋆}`, and `π^master_ℓ` is supervised by `𝒯_ℓ`. -/
theorem lemma4_5_q_supervision
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (E : EpisodeEst X A) (sel : Selector A) (hsel : IsArgmaxSelector sel) :
    (∀ lst, 1 ≤ lst → lst ≤ ℓmax → IsAdmissible M H (layerSup H ℓmax E sel lst) →
      IsQSupervised H (masterLe H ℓmax (basePolicies H ℓmax E sel) lst)
        (layerSup H ℓmax E sel lst)) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax → IsAdmissible M H (layerSup H ℓmax E sel ℓ) →
      IsQSupervised H (masterEq H ℓmax (basePolicies H ℓmax E sel) ℓ)
        (layerSup H ℓmax E sel ℓ)) := by sorry

end CorruptRobustRL.Supervised
