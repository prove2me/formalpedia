-- Prove2me | Theorems.Thm_CausalFailureRank_lemma_B_2
-- name    : CausalFailureRank.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:24.814856+00:00
-- url     : https://prove2.me/theorems/c64bd856-fe60-4391-b7d9-4080345afeda
-- title:
--   Lemma B.2 — full-history penalty bridge
-- statement:
--   From every healthy state at the first entry to stage $i$ with unused tools $R$, under every contract and all caps, every legal policy satisfies
--   $$\mathbb E[\text{future actual observation charges}]+\lambda\,\mathbb P(\text{eventual task failure})\ge G_{i,R}(\lambda),$$
--   including policies that delay an allocated correction, abandon before a write or continue to incur charges after permanent failure. This connects the recursion to the whole visible-history policy class.
--
--   Differences from the source:
--   - encoding: conditioning on generated history and private seed → a fixed seed (deterministic policy map) and a fixed healthy state with any history, integrating over the sample; reason: the tapes of stages not yet entered are independent of what was generated, so this is the conditional statement; averaging over the seed gives randomized policies
--   - reading: "healthy native history at the first entry" → stage $i$, open port, no reviews at $i$, unused tools $R$, each earlier error has a committed tool, and pending corrections only at earlier stages; reason: makes precise the source’s healthy state and App. E.2’s "first entry"
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.2, Lemma B.2, p.16

import Mathlib
import Definitions.Def_CausalFailureRank_G
import Definitions.Def_CausalFailureRank_step

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

open scoped Classical in
/-- **Lemma B.2 (Full-history penalty bridge).** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.2, p.16: "From every healthy native history
at the first entry to stage i, with unused tools R, every legal policy satisfies E[future actual
observation charges] + λP(eventual task failure) ≥ G_{i,R}(λ). This includes policies that delay an
already allocated correction, abandon before a write, or continue to incur charges after permanent
failure."

**Formalization Note.** The paper conditions on the generated history and the private seed. That is
this pointwise statement: fix the seed (a deterministic `π : History → Action`) and a healthy state with
any history, and integrate over the sample; the tapes of stages `≥ i` are independent of what was
generated. Averaging over the seed gives the randomized case. Holds for every contract and all caps. -/
theorem lemma_B_2 (I : Instance N q) (κ : Contract) (caps : Caps N) (π : History I → Action N q)
    (st : State I) (i : ℕ) (R : Finset (Fin q)) (hst : IsHealthyEntry I st i R) (lam : ℝ)
    (hlam : 0 < lam) :
    ENNReal.ofReal (G I i R lam) ≤
      ∫⁻ ω, obsBillFrom I κ caps π st ω +
          ENNReal.ofReal lam * (if SuccessFrom I κ caps π st ω then 0 else 1) ∂(tapeLaw I) := by sorry

end CausalFailureRank
