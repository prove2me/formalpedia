-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_claim4_8_layer_marginal
-- name    : CorruptRobustRL.Supervised.claim4_8_layer_marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:00.508087+00:00
-- url     : https://prove2.me/theorems/26ea90e0-5b53-4890-b9ec-201cf376775d
-- title:
--   Claim 4.8, p. 19 — under the layer schedule, $P[\ell_h=f]\le2^{1-f}$ for $f\in[\ell_{\max}]$, and $P[\ell_h=f]\le2^{-f}$ for $f>1$
-- statement:
--   Let $(\ell_1,\dots,\ell_H)\sim\mathcal D^{\mathrm{sched}}$ be the layer schedule of (3.3) with $H\ge1$ stages and $\ell_{\max}$ layers: $\ell_0=1$, and from layer $f$ the next layer is $n\in\{f+1,\dots,\ell_{\max}\}$ with probability $\frac1{2nH}2^{-(n-f)}$ and $f$ otherwise. Then for every stage $h\in[H]$ and every layer $f\in[\ell_{\max}]$,
--   $$P[\ell_h=f]\le2^{1-f},\qquad\text{and}\qquad P[\ell_h=f]\le2^{-f}\ \text{ if } f>1.$$
--
--   The schedule rarely reaches the robust layers; this bounds how much data each learner receives and feeds the visitation-ratio bounds of Lemma 4.10.
--
--   **Formalization Note** The stage is `t : Fin H`, the paper's $h=t+1$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 19, Claim 4.8

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset

/-- Claim 4.8 (p. 19): under the layer schedule, `P[ℓ_h = f] ≤ 2^{1−f}` for every stage and every
`f ∈ [ℓmax]`, and `P[ℓ_h = f] ≤ 2^{−f}` when `f > 1`. -/
theorem claim4_8_layer_marginal
    (H ℓmax : ℕ) (hH : 1 ≤ H) (t : Fin H) (f : ℕ) (hf : 1 ≤ f) (hfmax : f ≤ ℓmax) :
    layerProb H ℓmax t f ≤ (2 : ℝ) ^ (1 - (f : ℤ)) ∧
      (1 < f → layerProb H ℓmax t f ≤ (2 : ℝ) ^ (-(f : ℤ))) := by sorry

end CorruptRobustRL.Supervised
