-- Prove2me | Theorems.Thm_CompDesign_proposition_3_1
-- name    : CompDesign.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:53:18.779492+00:00
-- url     : https://prove2.me/theorems/82f06b39-59ba-4b58-9f0a-654091d16ee3
-- title:
--   Proposition 3.1 — the marginal-contribution rule is budget feasible
-- statement:
--   Let $B>0$ and let $v$ satisfy Assumption 3.1 ($v(\emptyset)=0$, monotone, submodular). Let $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8).
--
--   **Proposition 3.1 (Budget feasibility).** The marginal-contribution rule is budget feasible:
--   $$\sum_{i\in S}p^{mc}_i(S)\le B\qquad\forall S\subseteq N.$$
--
--   Budget feasibility is a requirement of the model on every payment rule (§3.1); this proposition certifies that $\Gamma^{mc}$ is a game of the model. It follows from Lemma 3.2, $\sum_{i\in S}(v(S)-v(S\setminus\{i\}))\le v(S)$.
--
--   Differences from the source: none.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §3.2.2, Proposition 3.1, p.16 (PDF 19)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay

open CompDesignBFM

namespace CompDesign

/-- Proposition 3.1 (Budget feasibility), §3.2.2, p.16 (PDF 19) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…):
the marginal-contribution rule (8) is budget feasible, `∑_{i∈S} p^mc_i(S) ≤ B` for all `S ⊆ N`.

**Formalization Note.** Assumption 3.1 and `B > 0` are the standing assumptions of §3.1. -/
theorem proposition_3_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (hv0 : v ∅ = 0)
    (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (S : Finset (Fin n)) :
    ∑ i ∈ S, mcPay v B S i ≤ B := by sorry

end CompDesign
