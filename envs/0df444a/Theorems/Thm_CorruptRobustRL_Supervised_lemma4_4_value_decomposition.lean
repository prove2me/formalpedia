-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_lemma4_4_value_decomposition
-- name    : CorruptRobustRL.Supervised.lemma4_4_value_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:10.02798+00:00
-- url     : https://prove2.me/theorems/928e9a29-5b1d-4378-aabc-7bff5869ff9e
-- title:
--   Lemma 4.4, p. 17 — $V^\star-V^{\pi^{\mathrm{master}}}=q_{\le\ell_\star}(V^\star-V^{\pi^{\mathrm{master}}_{\le\ell_\star}})+\sum_{\ell>\ell_\star}q_\ell(V^\star-V^{\pi^{\mathrm{master}}_\ell})$
-- statement:
--   Fix the nominal MDP, a horizon $H\ge1$, a number of layers $\ell_{\max}$ and arbitrary deterministic base policies $\pi^{\mathrm{base}}_1,\dots,\pi^{\mathrm{base}}_{\ell_{\max}}$. Let $\pi^{\mathrm{master}}$ be the master policy driven by the layer schedule $\mathcal D^{\mathrm{sched}}$ of (3.3), and $\pi^{\mathrm{master}}_\ell$, $\pi^{\mathrm{master}}_{\le\ell}$ the master policies conditioned on the final layer $\ell_H=\ell$ and $\ell_H\le\ell$, with $q_\ell=P[\ell_H=\ell]$ and $q_{\le\ell}=P[\ell_H\le\ell]$.
--
--   For every $\ell_\star\in\{1,\dots,\ell_{\max}\}$,
--   $$V^\star-V^{\pi^{\mathrm{master}}}=q_{\le\ell_\star}\big(V^\star-V^{\pi^{\mathrm{master}}_{\le\ell_\star}}\big)+\sum_{\ell_\star<\ell\le\ell_{\max}}q_\ell\big(V^\star-V^{\pi^{\mathrm{master}}_\ell}\big).$$
--
--   This is the law of total probability over the final layer; it splits the per-episode regret into the part charged to the under-robust learners $\ell\le\ell_\star$ and the parts charged to each robust learner $\ell>\ell_\star$.
--
--   **Formalization Note** The base policies are arbitrary: the identity is a property of the schedule alone.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 17, Lemma 4.4

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset

/-- Lemma 4.4 (p. 17): for any `ℓ⋆ ∈ [ℓmax]` (here `lst`) and any base policies,
`V⋆ − V^{π^master} = q_{≤ℓ⋆}(V⋆ − V^{π^master_{≤ℓ⋆}}) + Σ_{ℓ>ℓ⋆} q_ℓ (V⋆ − V^{π^master_ℓ})`. -/
theorem lemma4_4_value_decomposition
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (base : ℕ → DetPolicy X A) (lst : ℕ) (hlst : 1 ≤ lst) (hlstmax : lst ≤ ℓmax) :
    Vstar0 M H - mixValue M H (master H ℓmax base) =
      qLe H ℓmax lst * (Vstar0 M H - mixValue M H (masterLe H ℓmax base lst)) +
        ∑ ℓ ∈ Ioc lst ℓmax, q H ℓmax ℓ * (Vstar0 M H - mixValue M H (masterEq H ℓmax base ℓ)) := by sorry

end CorruptRobustRL.Supervised
