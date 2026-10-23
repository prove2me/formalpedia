-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_3
-- name    : FairRentFPTAS.Approx.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:45.149115+00:00
-- url     : https://prove2.me/theorems/9b968b36-abdf-47b4-92ad-abcfffe5e9dd
-- title:
--   Lemma 3, p. 11 — every iterate of Algorithm 1 is envy-free for Î, and lines 6–7 are well defined
-- statement:
--   Let $J$ be an instance with well-formed utilities, $M$ a threshold with $v_a(r,M)<v_a(r',0)$ for all $a,r,r'$, and $(\pi^i,p^i)_{0\le i\le T}$ a run of Algorithm 1 on $J$. For every $i\le T$:
--   1. $(\pi^i,p^i)$ is an envy-free solution of $\hat{\mathcal I}$;
--   2. $\mathcal F^w(p^i)$ (for $\hat{\mathcal I}$) has a maximum-weight perfect matching;
--   3. for every maximum-weight perfect matching $\sigma$ of $\mathcal F^w(p^i)$, the linear program $\mathrm{LP}(L^i,U^i,\sigma)$ has an optimal solution.
--
--   Items 2 and 3 are the claims of the proof ("$\pi^i$ is well defined", "it has an optimal solution") that make every iteration executable.
--
--   **Formalization Note** In this encoding item 1 is immediate from the definition of a run (the LP's constraints contain envy-freeness), so the statement also carries the well-definedness claims of the proof, which are its substance here.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 11, Lemma 3 and its proof (pp. 11–12)

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 3, p. 11, with the well-definedness claims of its proof: every iterate
`(πⁱ, pⁱ)` of Algorithm 1 is envy-free for `Î`, `F_w(pⁱ)` has a maximum-weight perfect matching,
and for every such matching `σ` the linear program `LP(Lⁱ, Uⁱ, σ)` has an optimal solution. -/
theorem lemma_3 {n : ℕ} (J : Instance n) (M : ℝ) (hJ : Standing J) (hM : IsThreshold J M)
    (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ) (hrun : IsRun J M T π p) :
    ∀ i ≤ T, IsEF (hatInst M J) (π i) (p i) ∧
      (∃ σ, IsMaxWeightPM (hatInst M J) (p i) σ) ∧
      ∀ σ, IsMaxWeightPM (hatInst M J) (p i) σ →
        ∃ q, IsLPOpt (hatInst M J) (domL (hatInst M J) (p i)) (domU (hatInst M J) (p i)) σ q := by sorry

end FairRentFPTAS.Approx
