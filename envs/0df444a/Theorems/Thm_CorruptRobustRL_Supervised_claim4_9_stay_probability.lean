-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_claim4_9_stay_probability
-- name    : CorruptRobustRL.Supervised.claim4_9_stay_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:06.423442+00:00
-- url     : https://prove2.me/theorems/4b775408-f8b4-44fc-801a-27441986ba6f
-- title:
--   Claim 4.9, p. 19 — $P[\ell_H=f\mid\ell_h=f]\ge1/e$, stated as $P[\ell_h=f,\ \ell_H=f]\ge\frac1e P[\ell_h=f]$
-- statement:
--   Let $(\ell_1,\dots,\ell_H)\sim\mathcal D^{\mathrm{sched}}$ be the layer schedule of (3.3) with $H\ge1$ stages and $\ell_{\max}$ layers. For every stage $h\in[H]$ and every layer $f\in[\ell_{\max}]$,
--   $$P[\ell_h=f,\ \ell_H=f]\ \ge\ \frac1e\,P[\ell_h=f],$$
--   that is, $P[\ell_H=f\mid\ell_h=f]\ge1/e$ whenever $P[\ell_h=f]>0$.
--
--   Once the schedule is at a layer, it stays there for the rest of the episode with constant probability; this is what makes the UCB visitation ratio of the master policies bounded.
--
--   **Formalization Note** The conditional probability is multiplied out so that the statement makes sense when $P[\ell_h=f]=0$. The printed proof uses $(1-1/H)^{H-h}\ge(1-1/H)^H\ge1/e$, whose last step fails for $H\ge2$; the claim itself holds, since $H-h\le H-1$ and $(1-1/H)^{H-1}\ge1/e$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 19, Claim 4.9

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset

/-- Claim 4.9 (p. 19), multiplied out: `P[ℓ_h = f ∧ ℓ_H = f] ≥ (1/e) · P[ℓ_h = f]`, i.e.
`P[ℓ_H = f | ℓ_h = f] ≥ 1/e` whenever the conditioning event has positive probability. -/
theorem claim4_9_stay_probability
    (H ℓmax : ℕ) (hH : 1 ≤ H) (t : Fin H) (f : ℕ) (hf : 1 ≤ f) (hfmax : f ≤ ℓmax) :
    1 / Real.exp 1 * layerProb H ℓmax t f ≤ layerStayProb H ℓmax t f := by sorry

end CorruptRobustRL.Supervised
